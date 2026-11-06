-- Prove2me | Theorems.Thm_SKAnnealing_Sampling_lemma_4_1
-- name    : SKAnnealing.Sampling.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:36.04969+00:00
-- url     : https://prove2.me/theorems/0f26842b-88a0-4ae4-ab15-2a05b6e664fb
-- title:
--   Lemma 4.1, p. 16 — $\|K\mathbf{Cov}-\mathrm{Id}\|_{\mathrm{op}}\le O(1)$ with probability $1-O(N^{-a})$
-- statement:
--   Throughout, $0<\beta<1$, $W\sim\mathrm{GOE}(N)$, $x\sim\mathrm{Unif}\{\pm1\}^N$ and $g\sim\mathcal N(0,\mathrm{Id})$ are independent, $\mu_t$ is the measure of Theorem 1.4, $\mathbf{Cov}=\mathbf{Cov}(\mu_t)$, and $K$, $m$, $v_i$, $q_N$, $d_i$, $\lambda_i$, $f_i$ are the TAP quantities (8) at $\mu_t$, with $M=W+\frac\beta Nxx^\top$ (diagonal zeroed).
--
--   **Lemma 4.1 (Operator norm of the residual).** For every $T>0$ and every constant $a>0$ there are constants $C_1$, $C_2$ and $N_0$ such that for all $N\ge N_0$ and all $t\in(0,T]$,
--   $$\Pr\Big[\big\|K\mathbf{Cov}-\mathrm{Id}\big\|_{\mathrm{op}}>C_1\Big]\le C_2\,N^{-a},$$
--   where $\|\cdot\|_{\mathrm{op}}$ is the Euclidean operator norm.
--
--   Combined with the lower bound $K\succeq\gamma$ of Lemma 5.1, it yields the covariance bound $\|\mathbf{Cov}(\mu_t)\|_{\mathrm{op}}=O(1)$ of Theorem 1.4.
--
--   Differences from the source:
--   - reading: fix t > 0 bounded, possibly decaying with N → one N₀ and one constant serve every t ∈ (0, T], for every T > 0; reason: a bound uniform over t ∈ (0, T] is equivalent to the bound for every sequence t_N ∈ (0, T], which is what "possibly decaying with N" requires (reading R5)
--   - encoding: with probability 1 − O(N^{−a}), ∥KCov − Id∥_op ⩽ O(1) → ∃ C, N₀ such that for every N ≥ N₀ the measure of the failure event is ≤ C·N^{−a}; reason: O(·) is a constant; the probability is written as the bound on the bad set (reading R4)
--   - reading: O(1) → a constant C₁ that may depend on β, T and a; reason: constants of the paper depend on the statement's fixed parameters unless it says otherwise; the proof takes C from Lemma 4.4's C_a (reading R3)
--   - encoding: W ∼ GOE(N), a symmetric matrix with diagonal entries → the off-diagonal entries W_{ik}, i < k, iid N(0, 1/N) (OAI.CriticalSK.disorderLaw); no diagonal; reason: σ_i² = 1, so the diagonal only adds a constant to the Hamiltonian and changes no Gibbs measure, kernel or covariance (reading R8)
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), Lemma 4.1, p. 16 (PDF p. 18)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_SKAnnealing_Sampling_tilt
import Definitions.Def_SKAnnealing_Sampling_plantedTilted
import Definitions.Def_SKAnnealing_Sampling_tapHessian

open OAI.CriticalSK MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKAnnealing.Sampling

/-- **Lemma 4.1** (operator norm of the residual). For any constant `a > 0`, with probability `1 − O(N^{−a})`,
`‖K Cov − Id‖_op ≤ O(1)`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), Lemma 4.1, p. 16 (PDF p. 18).

**Formalization Note** Standing setting of Section 4 (`0 < β < 1`, `plantedFieldLaw`, `µ_t = plantedTilted`,
`M = plantedMatrix`), uniformly over `t ∈ (0, T]` for `N ≥ N₀` (R5). `O(1)` is a constant `C₁` and
`O(N^{−a})` is `C₂ N^{−a}`, both depending on `β, T, a` (R3, R4). `‖·‖_op` is the Euclidean operator norm. -/
theorem lemma_4_1 :
    ∀ β : ℝ, 0 < β → β < 1 → ∀ T : ℝ, 0 < T → ∀ a : ℝ, 0 < a →
      ∃ C₁ C₂ : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ, 0 < t → t ≤ T →
        plantedFieldLaw N {ω |
            let M := plantedMatrix β ω.1.1 ω.1.2
            let μ := plantedTilted β t ω.1.1 ω.1.2 ω.2
            C₁ < ‖(tapHessian β M μ * lawCov μ - 1).toEuclideanLin.toContinuousLinearMap‖}
          ≤ ENNReal.ofReal (C₂ * (N : ℝ) ^ (-a)) := by sorry

end SKAnnealing.Sampling
