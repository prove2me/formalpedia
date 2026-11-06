-- Prove2me | Theorems.Thm_SKAnnealing_Sampling_lemma_4_4
-- name    : SKAnnealing.Sampling.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:37.35091+00:00
-- url     : https://prove2.me/theorems/bc0564ee-36a6-4344-918c-572dc0c5a622
-- title:
--   Lemma 4.4, p. 16 — off-diagonal residual: $\sum_i\|f_i-\lambda_i\mathbf{Cov}_{-i,i}\|_2^2\le C_a$ with probability $1-N^{-a}$
-- statement:
--   Throughout, $0<\beta<1$, $W\sim\mathrm{GOE}(N)$, $x\sim\mathrm{Unif}\{\pm1\}^N$ and $g\sim\mathcal N(0,\mathrm{Id})$ are independent, $\mu_t$ is the measure of Theorem 1.4, $\mathbf{Cov}=\mathbf{Cov}(\mu_t)$, and $K$, $m$, $v_i$, $q_N$, $d_i$, $\lambda_i$, $f_i$ are the TAP quantities (8) at $\mu_t$, with $M=W+\frac\beta Nxx^\top$ (diagonal zeroed).
--
--   **Lemma 4.4.** For every $T>0$ and every constant $a>0$ there are a constant $C_a$ and $N_0$ such that for all $N\ge N_0$ and all $t\in(0,T]$,
--   $$\Pr\Big[\sum_{i\in[N]}\big\|f_i-\lambda_i\mathbf{Cov}_{-i,i}\big\|_2^2>C_a\Big]\le N^{-a}.$$
--
--   This is the off-diagonal half of the bound on $K\mathbf{Cov}-\mathrm{Id}$: after removing the diagonal correction $\lambda_i\mathbf{Cov}_{-i,i}$ from each row, the remaining residual has bounded Frobenius norm. Together with Lemma 4.5 it gives Lemma 4.1.
--
--   Differences from the source:
--   - reading: fix t > 0 bounded, possibly decaying with N → one N₀ and one constant serve every t ∈ (0, T], for every T > 0; reason: a bound uniform over t ∈ (0, T] is equivalent to the bound for every sequence t_N ∈ (0, T], which is what "possibly decaying with N" requires (reading R5)
--   - encoding: Pr[…] ⩽ N^{−a} → for every N ≥ N₀, the measure of the failure event is ≤ N^{−a} (constant 1 kept); reason: the bound is asymptotic in N; the constant 1 of the page is kept (reading R4)
--   - encoding: W ∼ GOE(N), a symmetric matrix with diagonal entries → the off-diagonal entries W_{ik}, i < k, iid N(0, 1/N) (OAI.CriticalSK.disorderLaw); no diagonal; reason: σ_i² = 1, so the diagonal only adds a constant to the Hamiltonian and changes no Gibbs measure, kernel or covariance (reading R8)
--   - encoding: vectors indexed by [N] ∖ {i} and ‖·‖₂² → vectors of ℝ^N with entry i set to 0, and the sum of squared entries; reason: the same numbers; Lean's default norm on Fin N → ℝ is the sup norm, so the Euclidean square is written out
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), Lemma 4.4, p. 16 (PDF p. 18)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_SKAnnealing_Sampling_tilt
import Definitions.Def_SKAnnealing_Sampling_plantedTilted
import Definitions.Def_SKAnnealing_Sampling_tapHessian

open OAI.CriticalSK MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKAnnealing.Sampling

/-- **Lemma 4.4** (off-diagonal residual). For every constant `a > 0` there is a constant `C_a` such that
`Pr[∑_{i ∈ [N]} ‖f_i − λ_i Cov_{−i,i}‖_2^2 > C_a] ≤ N^{−a}`, where `f_i = (K Cov − Id)_{i,−i}`,
`λ_i = β²(1 − q_N) − β d_iᵀ M_{i,−i}` and `d_i = Cov_{i,−i}/v_i`, all at the measure `µ_t` of Theorem 1.4.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), Lemma 4.4, p. 16 (PDF p. 18).

**Formalization Note** Standing setting of Section 4: `0 < β < 1`, `(W, x, g)` drawn from `plantedFieldLaw N`,
`M = plantedMatrix β W x` (zero diagonal), `µ_t = plantedTilted β t W x g`. Reading R5: "fix `t > 0` bounded"
is uniformity over `t ∈ (0, T]` for `N ≥ N₀`. The vectors `f_i`, `Cov_{−i,i}` are vectors of `ℝ^N` with entry
`i` removed (set to `0`), and `‖·‖_2^2` is written as the sum of squares. The printed bound `N^{−a}` keeps
constant `1`; `N ≥ N₀` is reading R4. -/
theorem lemma_4_4 :
    ∀ β : ℝ, 0 < β → β < 1 → ∀ T : ℝ, 0 < T → ∀ a : ℝ, 0 < a →
      ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ, 0 < t → t ≤ T →
        plantedFieldLaw N {ω |
            let M := plantedMatrix β ω.1.1 ω.1.2
            let μ := plantedTilted β t ω.1.1 ω.1.2 ω.2
            C < ∑ i : Fin N, ∑ j : Fin N,
              (residualRow β M μ i j - cavityLam β M μ i * (if j = i then 0 else lawCov μ j i)) ^ 2}
          ≤ ENNReal.ofReal ((N : ℝ) ^ (-a)) := by sorry

end SKAnnealing.Sampling
