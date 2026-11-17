-- Prove2me | Theorems.Thm_ReplicableOL_Supplement_theorem_4
-- name    : ReplicableOL.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:24:12.322703+00:00
-- url     : https://prove2.me/theorems/19891f61-6602-4dea-97fd-1522d6451133
-- title:
--   Theorem 4 (precise form) — DALR gambles on the triangle wave: $\mathbb E_R[(\mathrm{Reg}_T)_+]\ge \bar K^{1/4}T^{7/8}/(2230\rho^{1/4})$
-- statement:
--   Fix a DALR chain $T=A_0>A_1>\dots>A_K=B\ge1$ and a level scale $H$, and write $\Sigma_1=\sum_{j=2}^{K}A_j/2$ and $\Pi=T/(2A_1)$. Let $S^\triangle$ be the triangle wave with half-period $A_1$.
--
--   1. If $K\ge2$, $2\Sigma_1+B\le A_1/48$, $\Pi\ge116$ and $3A_1\le 4H$, then on $S^\triangle$
--
--   $$
--   \mathbb E_R\big[(\mathrm{Reg}_T)_+\big]\ \ge\ \frac{A_1}{H}\cdot\frac{\sqrt{TA_1}}{243},\qquad\text{while}\qquad \mathbb E_R\,\mathrm{Reg}_T\ \le\ \Pi B .
--   $$
--
--   2. Under the parameters of Theorem 3 ($\rho\in(0,1]$, $T$ a power of $2$, $H$, $\kappa$ and the chain as there), if $T\ge 8\cdot10^{18}\,\bar K^2/\rho^2$, then the four hypotheses of part 1 hold, and
--
--   $$
--   \mathbb E_R\big[(\mathrm{Reg}_T)_+\big]\ \ge\ \frac{\sqrt{TA_1}}{1771},\qquad \mathbb E_R\big[(\mathrm{Reg}_T)_+\big]\ \ge\ \frac{\bar K^{1/4}\,T^{7/8}}{2230\,\rho^{1/4}},
--   $$
--
--   with half-period $A_1\in[0.634,\,1.27)\cdot\sqrt{\bar K}\,T^{3/4}/\sqrt\rho$.
--
--   Here $(\mathrm{Reg}_T)_+=\max(\mathrm{Reg}_T,0)$ and $\mathbb E_R$ is the expectation over DALR's seed alone. Together with Theorem 3, part 2 shows that DALR's positive-part regret on a single deterministic sequence exceeds its $O(T^{3/4})$ expected regret by a factor of order $T^{1/8}\rho^{1/4}$: the algorithm "gambles", which is the phenomenon the paper's title refers to.
--
--   **Formalization Note** The positive part is taken inside the seed integral. In part 2 the existence of Theorem 3's chain is a conclusion, the hypotheses and bounds are stated for every chain satisfying `IsThm3Chain`, and $\bar K\ge1$ is assumed (Theorem 3's parameters are undefined otherwise).
--
--   Differences from the source:
--   - encoding: rounds 1, …, T, experts 1, 2, levels 1, …, K → 0-based Fin T rounds, Lean expert 0 = expert 1, seed level index i : Fin K = level i+1; reason: Lean indexing; the same algorithm and the same sequences
--   - encoding: E_R[(Reg_T)_+] → ∫ max (regret …) 0 over the seed law; reason: the positive part is taken inside the expectation, as on the page
--   - encoding: Σ_1 = Σ_{j>1} A_j/2, Π = T/(2A_1), B = A_K → (Σ_{j ∈ [2, K]} A_j)/2, (T : ℝ)/(2 A_1), C.A C.K; reason: the definitions of p.19 and p.21 written out
--   - encoding: under the parameters of Theorem 3 (with K̄ = ⌈log₂ log₂ T⌉) → 1 ≤ K̄ added in Part 2; reason: for K̄ ≤ 0 (T ∈ {1, 2}) Theorem 3's H and κ are undefined (division by K̄ = 0, or K̄ = −∞); the condition excludes only these undefined cases
--   - encoding: under the parameters of Theorem 3 these hypotheses hold … and then … → Part 2 asserts that Theorem 3's chain exists, and that for every chain C with IsThm3Chain ρ C and H = thm3H the four hypotheses and the three conclusions hold; reason: IsThm3Chain fixes the chain DALR reads, so this is the paper's single run; its existence is asserted rather than assumed
--   - encoding: decimal constants 48, 116, 243, 8 · 10¹⁸, 1771, 2230, 0.634, 1.27 → the same decimals, read as exact rationals; reason: Lean convention; same values
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Theorem 4 (precise form), p.21; informal form p.4; proof App. A.11, pp.43–44

import Mathlib
import Definitions.Def_ReplicableOL_regret
import Definitions.Def_ReplicableOL_Supplement_seedLaw
import Definitions.Def_ReplicableOL_Supplement_dalr
import Definitions.Def_ReplicableOL_Supplement_triWave
import Definitions.Def_ReplicableOL_Supplement_IsThm3Chain
open MeasureTheory ProbabilityTheory

namespace ReplicableOL.Supplement

/-- **Theorem 4 (precise form).** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Theorem 4 (precise form), p.21; informal form p.4; proof App. A.11, pp.43–44. "Run DALR with any chain and level scale such that K ≥ 2, 2Σ_1 + B ≤ A_1/48, Π ≥ 116 and 3A_1 ≤ 4H. Then on S^△ E_R[(Reg_T)_+] ≥ (A_1/H) · √(TA_1)/243, while E_R Reg_T ≤ ΠB. Under the parameters of Theorem 3 these hypotheses hold when T ≥ 8 · 10¹⁸ K̄²/ρ², and then E_R[(Reg_T)_+] ≥ √(TA_1)/1771 and E_R[(Reg_T)_+] ≥ K̄^{1/4} T^{7/8}/(2230 ρ^{1/4}), with half-period A_1 ∈ [0.634, 1.27) · √K̄ T^{3/4}/√ρ."

Part 1 holds for every DALR chain `C` and level scale `H`; Part 2 for Theorem 3's chain and `H`. Here `Σ_1 = Σ_{j=2}^K A_j/2` (p.19: `Σ_i := Σ_{j>i} A_j/2`), `Π = T/(2A_1)`, `B = A_K`, and `S^△ = triWave T A_1` uses the chain's own `A_1`.

**Formalization Note.** `(Reg_T)_+` is `max (Reg_T) 0` inside the seed integral. In Part 2, `1 ≤ K̄` excludes `T ∈ {1, 2}`, where Theorem 3's `H, κ` are undefined (`K̄ ≤ 0`); the chain's existence is a conclusion. Decimal constants are exact rationals. -/
theorem theorem_4 :
    (∀ (T : ℕ) (C : Chain T) (H : ℝ), 2 ≤ C.K →
      2 * ((∑ j ∈ Finset.Icc 2 C.K, (C.A j : ℝ)) / 2) + C.A C.K ≤ (C.A 1 : ℝ) / 48 →
      116 ≤ (T : ℝ) / (2 * C.A 1) →
      3 * (C.A 1 : ℝ) ≤ 4 * H →
      (C.A 1 : ℝ) / H * (√((T : ℝ) * C.A 1) / 243) ≤
          ∫ r, max (ReplicableOL.regret (dalr C) (triWave T (C.A 1)) r) 0 ∂(seedLaw C H) ∧
        ∫ r, ReplicableOL.regret (dalr C) (triWave T (C.A 1)) r ∂(seedLaw C H) ≤
          (T : ℝ) / (2 * C.A 1) * C.A C.K) ∧
    (∀ (ρ : ℝ) (T : ℕ), 0 < ρ → ρ ≤ 1 → (∃ e : ℕ, T = 2 ^ e) → 1 ≤ Kbar T →
      8 * 10 ^ 18 * (Kbar T : ℝ) ^ 2 / ρ ^ 2 ≤ (T : ℝ) →
      (∃ C : Chain T, IsThm3Chain ρ C) ∧
      ∀ C : Chain T, IsThm3Chain ρ C →
        2 ≤ C.K ∧
        2 * ((∑ j ∈ Finset.Icc 2 C.K, (C.A j : ℝ)) / 2) + C.A C.K ≤ (C.A 1 : ℝ) / 48 ∧
        116 ≤ (T : ℝ) / (2 * C.A 1) ∧
        3 * (C.A 1 : ℝ) ≤ 4 * thm3H ρ T ∧
        √((T : ℝ) * C.A 1) / 1771 ≤
          ∫ r, max (ReplicableOL.regret (dalr C) (triWave T (C.A 1)) r) 0
            ∂(seedLaw C (thm3H ρ T)) ∧
        (Kbar T : ℝ) ^ (1 / 4 : ℝ) * (T : ℝ) ^ (7 / 8 : ℝ) / (2230 * ρ ^ (1 / 4 : ℝ)) ≤
          ∫ r, max (ReplicableOL.regret (dalr C) (triWave T (C.A 1)) r) 0
            ∂(seedLaw C (thm3H ρ T)) ∧
        0.634 * (√(Kbar T : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) / √ρ) ≤ (C.A 1 : ℝ) ∧
        (C.A 1 : ℝ) < 1.27 * (√(Kbar T : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) / √ρ)) := by sorry

end ReplicableOL.Supplement
