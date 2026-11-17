-- Prove2me | Theorems.Thm_ReplicableOL_Supplement_theorem_3
-- name    : ReplicableOL.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:23:01.909212+00:00
-- url     : https://prove2.me/theorems/439fe99a-8039-4503-ace7-5a292864e48b
-- title:
--   Theorem 3 (with parameters) — DALR is adversarially $\rho$-replicable with $\mathbb E_R\mathrm{Reg}_T\le 1.97\sqrt{\bar K}T^{3/4}/\sqrt\rho$
-- statement:
--   Let $\rho\in(0,1]$, let $T$ be a power of $2$, let $\bar K=\lceil\log_2\log_2T\rceil$, and assume
--
--   $$
--   T\ \ge\ T_U(\rho):=\max\Big\{\frac{10.4\,\bar K^2}{\rho^2},\ \frac{6.2\cdot10^4\,\rho^2}{\bar K^2}\Big\}.
--   $$
--
--   Run DALR with the level scale and chain
--
--   $$
--   H=4.62\sqrt{\bar K}\,\frac{T^{3/4}}{\sqrt\rho},\qquad \kappa=\frac{\rho H}{2.93\,\bar K\,T},\qquad A_0=T,\quad A_i=2^{\lceil\log_2(\sqrt{A_{i-1}}/\kappa)\rceil}\ (i\ge1),
--   $$
--
--   stopping at the first $K$ with $A_K\le 8/\kappa^2$. Then:
--
--   1. the chain is well defined: such a $K$ exists and $A_0>A_1>\dots>A_K\ge1$ are powers of $2$, each dividing the previous one;
--   2. DALR is adversarially $\rho$-replicable: under every product law of the loss sequence on $([0,1]^2)^T$, two runs on independent samples with a shared seed produce different trajectories with probability at most $\rho$;
--   3. for every loss sequence $S\in([0,1]^2)^T$, the expected regret over the seed satisfies
--
--   $$
--   \mathbb E_R\,\mathrm{Reg}_T(S,R)\ \le\ 1.97\,\sqrt{\bar K}\,\frac{T^{3/4}}{\sqrt\rho}.
--   $$
--
--   This is the upper bound of the paper: it matches the $T^{3/4}/\sqrt\rho$ rate of the typical-case lower bound (Theorem 1) up to the factor $\sqrt{\bar K}$ and the dependence on the gap, and it improves on the $\tilde O(T^{5/6}\rho^{-1/3})$ bound of earlier replicable experts algorithms.
--
--   **Formalization Note** DALR is the learner `dalr C` with seed law `seedLaw C H`; replicability is the published `IsAdvReplicable` and regret the published realized `regret`. The chain's existence is stated as a conclusion, and the remaining conclusions are stated for every chain satisfying `IsThm3Chain`, which pins the chain down on all indices DALR reads.
--
--   Differences from the source:
--   - encoding: rounds 1, …, T, experts 1, 2, levels 1, …, K → 0-based Fin T rounds, Lean expert 0 = expert 1, seed level index i : Fin K = level i+1; reason: Lean indexing; the same algorithm and the same sequences
--   - encoding: T ≥ T_U(ρ) with K̄ = ⌈log₂ log₂ T⌉ → 1 ≤ K̄ and max{10.4 K̄²/ρ², 6.2·10⁴ ρ²/K̄²} ≤ T; reason: for K̄ ≤ 0 (T ∈ {1, 2}) the paper's T_U(ρ) is +∞ (division by K̄² = 0, or K̄ = −∞) and H, κ are undefined, while Lean's x/0 = 0 would make T_U = 0; 1 ≤ K̄ excludes exactly these undefined cases
--   - encoding: Run DALR with A_i := 2^{⌈log₂(√A_{i−1}/κ)⌉}, stopping at the first K with A_K ≤ 8/κ² → the existence of a Chain C with IsThm3Chain ρ C is a conclusion, and the remaining conclusions hold for every such C; reason: IsThm3Chain fixes K and A_0, …, A_K, which is all DALR reads, so this is the paper's single DALR, and its well-definedness is asserted rather than assumed
--   - encoding: exponent ⌈log₂(√A_{i−1}/κ)⌉ ∈ ℤ → Int.toNat of the ceiling; reason: for the indices DALR reads the exponent is positive, so toNat is the identity there
--   - encoding: E_R over χ ∼ U[−H, H], ω_{i,q} ∼ U[0, A_i) independent; every sequence S → Bochner integral of the published regret over the product of conditioned Lebesgue measures; S : Fin T → Fin 2 → ℝ with entries in [0, 1]; reason: the same law and the same sequences; the regret is bounded and measurable, so the integral is the expectation
--   - encoding: decimal constants 10.4, 6.2 · 10⁴, 4.62, 2.93, 8, 1.97 → the same decimals, read as exact rationals; reason: Lean convention; same values
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Theorem 3 (with parameters), p.20; informal form p.4; arithmetic App. A.11(a)–(d), pp.42–43

import Mathlib
import Definitions.Def_ReplicableOL_regret
import Definitions.Def_ReplicableOL_IsAdvReplicable
import Definitions.Def_ReplicableOL_Supplement_seedLaw
import Definitions.Def_ReplicableOL_Supplement_dalr
import Definitions.Def_ReplicableOL_Supplement_IsThm3Chain
open MeasureTheory ProbabilityTheory

namespace ReplicableOL.Supplement

/-- **Theorem 3 (with parameters).** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Theorem 3 (with parameters), p.20; informal form p.4; arithmetic App. A.11, pp.42–43. "Let ρ ∈ (0, 1], T a power of 2, K̄ = ⌈log₂ log₂ T⌉, and T ≥ T_U(ρ) := max{10.4 K̄²/ρ², 6.2 · 10⁴ ρ²/K̄²}. Run DALR with H := 4.62 √K̄ T^{3/4}/√ρ, κ := ρH/(2.93 K̄ T), A_i := 2^{⌈log₂(√A_{i−1}/κ)⌉} (i ≥ 1), stopping at the first K with A_K ≤ 8/κ². Then DALR is adversarially ρ-replicable. For every sequence S, its expected regret satisfies E_R Reg_T(S, R) ≤ 1.97 √K̄ T^{3/4}/√ρ."

Conclusions: the chain exists (the algorithm is well defined), and for it DALR with seed law `seedLaw C H` is adversarially ρ-replicable and has expected regret at most `1.97 √K̄ T^{3/4}/√ρ` on every `S ∈ ([0,1]²)^T`.

**Formalization Note.** `1 ≤ K̄` is the paper's `T ≥ T_U(ρ)` at `K̄ ≤ 0` (`T ∈ {1, 2}`), where `T_U(ρ) = +∞` (division by `K̄² = 0`, or `K̄ = −∞`) and `H, κ` are undefined; Lean's `x/0 = 0` would otherwise make `T_U = 0`. Adversarial replicability is the published `IsAdvReplicable` (every product law on `([0,1]²)^T`, point masses included); regret is the published realized `regret`, integrated over the seed law. Decimal constants are exact rationals. -/
theorem theorem_3 (ρ : ℝ) (T : ℕ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hT : ∃ e : ℕ, T = 2 ^ e)
    (hK : 1 ≤ Kbar T)
    (hTU : max (10.4 * (Kbar T : ℝ) ^ 2 / ρ ^ 2) (6.2 * 10 ^ 4 * ρ ^ 2 / (Kbar T : ℝ) ^ 2) ≤ (T : ℝ)) :
    (∃ C : Chain T, IsThm3Chain ρ C) ∧
    ∀ C : Chain T, IsThm3Chain ρ C →
      ReplicableOL.IsAdvReplicable (dalr C) (seedLaw C (thm3H ρ T)) ρ ∧
      ∀ S : Fin T → Fin 2 → ℝ, (∀ t i, S t i ∈ Set.Icc (0 : ℝ) 1) →
        ∫ r, ReplicableOL.regret (dalr C) S r ∂(seedLaw C (thm3H ρ T)) ≤
          1.97 * √(Kbar T : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) / √ρ := by sorry

end ReplicableOL.Supplement
