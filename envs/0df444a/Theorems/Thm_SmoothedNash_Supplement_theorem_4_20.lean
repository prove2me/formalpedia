-- Prove2me | Theorems.Thm_SmoothedNash_Supplement_theorem_4_20
-- name    : SmoothedNash.Supplement.theorem_4_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:12:09.583995+00:00
-- url     : https://prove2.me/theorems/30189285-2986-447b-84eb-0164d539c7c4
-- title:
--   Theorem 4.20 — worst case: perturb, then Algorithm 4; $\varepsilon$-VI solution w.p. $\ge 1-p$ in time $C^n\varepsilon^{-3n}\log(4/p)^{1.5n}(1+L_0+L_1)^{3n-2}(1+L_0+L_1+L_2)^2p^{-2}$
-- statement:
--   Let $F : B(0,1) \to \mathbb R^n$ be a deterministic map satisfying Assumptions 1.8, 1.9 and 1.10 with constants $L_0, L_1, L_2$, and let $n \ge 2$, $0 < \varepsilon \le 1$, $0 < p < 1$.
--
--   **Theorem.** There is a universal constant $C$ and a randomized algorithm that finds an $\varepsilon$-approximate solution to the variational inequality for $F$ with probability at least $1 - p$ in runtime
--   $$
--   C^n \varepsilon^{-3n} \cdot \log(4/p)^{1.5n} \cdot (1 + L_0 + L_1)^{3n-2} (1 + L_0 + L_1 + L_2)^2 p^{-2} .
--   $$
--   The algorithm draws an $n \times n$ matrix $D$ and a vector $e$ with i.i.d. centered Gaussian entries of a variance $s$, and runs Algorithm 4 on $\tilde F(x) = F(x) + Dx + e$ with accuracy $\varepsilon/2$, bounds $L_0', L_1', L_2$ and a row-gap bound $\theta'$, where $s, L_0', L_1', \theta'$ depend only on $(n, \varepsilon, p, L_0, L_1, L_2)$. Precisely: such parameter choices exist so that, for every exponent $\kappa$ of the per-iteration arithmetic, there is a universal $C$ with the following property for every $F$: with probability at least $1 - p$ over $(D, e)$, a terminated run on $\tilde F$ exists, every run's runtime (including the $n^2 + n$ Gaussian draws) is at most the bound, and every terminated run outputs an $\varepsilon$-approximate VI solution for $F$ itself.
--
--   This turns the smoothed guarantee into a randomized worst-case algorithm with running time $(C/\varepsilon)^{O(n)}$ (Remark 1.16).
--
--   **Formalization Note** The probability bound is stated as: the outer measure of the failure set under the Gaussian law is at most $p$. $\log(4/p)^{1.5n}$ is a real power of a positive number.
--
--   Differences from the source:
--
--   - reading: there exists an algorithm → the paper's procedure (i.i.d. N(0, s) perturbation Dx + e, then Algorithm 4 on F̃ with accuracy ε/2, bounds L0', L1', L2 and row gap θ'), with ∃ s, L0', L1', θ' as functions of (n, ε, p, L0, L1, L2) chosen before F; reason: the algorithm of the proof; its numerical parameters may not depend on F; the proof's choice is one witness, and a bare existential over algorithms would be trivial
--   - reading: for all n ≥ 2, 0 < ε ≤ 1 and 0 < p < 1, there exists a universal constant C → ∃ C (for each κ) before n, ε, p and F; reason: a universal constant does not depend on n, ε, p
--   - reading: in runtime → alg4Runtime κ on F̃ plus (n² + n)(n+1)^κ for the Gaussian draws, bounded for every run, ∀ κ ∃ C; reason: the cost model of Theorem 4.5 with an unspecified polynomial; the draws are part of the algorithm
--   - reading: finds an ε-approximate solution with probability at least 1 − p → P_{D,e}(failure) ≤ p, where success = a terminated run on F̃ exists ∧ every run's runtime ≤ the bound ∧ every terminated run's output is an ε-approximate VI solution for F; reason: the full success event; the guarantee is for F, not F̃
--   - encoding: probability at least 1 − p → outer measure of the failure set under gaussPerturbLaw ≤ p; reason: no measurability of the event is needed; on a measurable event it is the same
--   - encoding: log(4/p)^{1.5n} → Real.log (4/p) ^ ((3/2) n) (real power); reason: log(4/p) > 0 for 0 < p < 1
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Theorem 4.20, p.43 (proof pp.43–44; Remark 1.16, p.6)

import Mathlib
import Definitions.Def_SmoothedNash_Supplement_IsApproxVI
import Definitions.Def_SmoothedNash_Supplement_BoundedNorm
import Definitions.Def_SmoothedNash_Supplement_LipschitzOnBall
import Definitions.Def_SmoothedNash_Supplement_JacobianLipschitz
import Definitions.Def_SmoothedNash_Supplement_IsAlg4Trace
import Definitions.Def_SmoothedNash_Supplement_IsAlg4Terminated
import Definitions.Def_SmoothedNash_Supplement_alg4Out
import Definitions.Def_SmoothedNash_Supplement_alg4Runtime
import Definitions.Def_SmoothedNash_Supplement_perturbMap
import Definitions.Def_SmoothedNash_Supplement_gaussPerturbLaw
open MeasureTheory

namespace SmoothedNash.Supplement

/-- **Theorem 4.20 (Worst-case algorithm)** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.43). For a function `F` that satisfies
Assumptions 1.8, 1.9 and 1.10, for all `n ≥ 2`, `0 < ε ≤ 1` and `0 < p < 1`, there exists a universal
constant `C`, such that there exists an algorithm that finds an `ε`-approximate solution to a
variational inequality with probability at least `1 − p` in runtime
`C^n ε^{−3n} · log(4/p)^{1.5n} · (1 + L0 + L1)^{3n−2} (1 + L0 + L1 + L2)^2 p^{−2}`.

The algorithm (proof of Theorem 4.20, pp.43–44) draws an `n × n` matrix `D` and a vector `e` with
i.i.d. centered Gaussian entries of variance `s`, and runs Algorithm 4 on `F̃(x) = F(x) + Dx + e` with
accuracy `ε/2`, bounds `L0', L1', L2` and row-gap bound `θ'`. Stated: there are parameter choices
`s, L0', L1', θ'`, functions of `(n, ε, p, L0, L1, L2)` only (never of `F`), such that for every cost
exponent `κ` there is a universal `C > 0` with the following: for every deterministic `F` satisfying
Assumptions 1.8–1.10, the probability over `(D, e)` that the following fails is at most `p`: a
terminated run on `F̃` exists, every run's running time (including the `n² + n` Gaussian draws) is at
most the bound, and every terminated run outputs an `ε`-approximate VI solution for `F` itself.

**Formalization Note** "There exists an algorithm" is stated for the paper's procedure (Gaussian
affine perturbation, then Algorithm 4), with its numerical parameters existentially quantified as
functions of `(n, ε, p, L0, L1, L2)` before `F` is chosen; the proof's choice
(`s = ε²/(C n log(4/p))`, `L0' = L0 + C(g_X + g_Y)√log(4/p)`, `L1' = L1 + C g_X √log(4/p)`, `θ` of
Theorem 4.17 with `2Pv, 2Pd`) is one witness. The running time is `alg4Runtime κ` plus
`(n² + n)(n + 1)^κ` for the draws; `C` depends only on `κ`. `log(4/p)^{1.5n}` is a real power. The
failure probability is the outer measure of the failure set under `gaussPerturbLaw`. -/
theorem theorem_4_20 :
    ∃ s L0' L1' θ' : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ, ∀ κ : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ}, 2 ≤ n → ∀ (ε p L0 L1 L2 : ℝ), 0 < ε → ε ≤ 1 → 0 < p → p < 1 →
      ∀ F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        BoundedNorm F L0 → LipschitzOnBall F L1 → JacobianLipschitz F L2 →
        gaussPerturbLaw n (s n ε p L0 L1 L2)
          {De | ¬ ((∃ q v N, IsAlg4Terminated (perturbMap F De.1 De.2) (L0' n ε p L0 L1 L2)
                  (L1' n ε p L0 L1 L2) L2 (ε / 2) (θ' n ε p L0 L1 L2) q v N) ∧
              (∀ q v N, IsAlg4Trace (perturbMap F De.1 De.2) (L0' n ε p L0 L1 L2)
                  (L1' n ε p L0 L1 L2) L2 (ε / 2) (θ' n ε p L0 L1 L2) q v N →
                alg4Runtime κ (perturbMap F De.1 De.2) (ε / 2) N
                    + ((n : ℝ) ^ 2 + n) * ((n : ℝ) + 1) ^ κ ≤
                  C ^ n * (ε ^ (3 * n))⁻¹ * Real.log (4 / p) ^ ((3 / 2 : ℝ) * n) *
                    (1 + L0 + L1) ^ (3 * n - 2) * (1 + L0 + L1 + L2) ^ 2 * (p ^ 2)⁻¹) ∧
              (∀ q v N, IsAlg4Terminated (perturbMap F De.1 De.2) (L0' n ε p L0 L1 L2)
                  (L1' n ε p L0 L1 L2) L2 (ε / 2) (θ' n ε p L0 L1 L2) q v N →
                IsApproxVI F ε (alg4Out (perturbMap F De.1 De.2) (L0' n ε p L0 L1 L2)
                  (L1' n ε p L0 L1 L2) (ε / 2) q N)))} ≤ ENNReal.ofReal p := by sorry

end SmoothedNash.Supplement
