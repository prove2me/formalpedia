-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_entropy_optimizations_attained
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.entropy_optimizations_attained
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:44:07.896363+00:00
-- url     : https://prove2.me/theorems/dc77988e-6b0b-4ebc-b291-b8bf7fd03c75
-- title:
--   Attainment of the six entropy optimizations
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. Here $H_{\min}(\rho_{AB}\mid\sigma_B)$ is the fixed-reference min entropy, and $H_{\max}(\rho_{AB}\mid\sigma_B)$ is the historical support-rank max entropy, $\log_2\operatorname{tr}[(I_A\otimes\sigma_B)\Pi_{\rho_{AB}}]$, where $\Pi_\rho$ is the support projector. A conditioning register in place of a reference density means a supremum over normalized reference densities. The superscript $\epsilon$ denotes optimization over normalized density operators at half trace-norm distance at most $\epsilon$: a supremum for fixed-reference min entropy and an infimum for fixed-reference rank-max entropy, followed by a supremum over normalized reference densities when conditioning on a register. Fix a density $\rho_{AB}$, a normalized reference $\sigma_B$, and $\epsilon\ge0$. The two unsmoothed optimized entropies have maximizing normalized reference densities; both fixed-reference smooth entropies have optimizing normalized densities in the closed smoothing ball; and both optimized smooth entropies have maximizing normalized reference densities. More explicitly, there exist density references $s_1,s_2,s_5,s_6$ and states $\tau_3,\tau_4$ in that ball such that
--
--   $$
--   \begin{aligned}
--   H_{\min}(\rho\mid B)&=H_{\min}(\rho\mid s_1),&H_{\max}(\rho\mid B)&=H_{\max}(\rho\mid s_2),\\
--   H_{\min}^{\epsilon}(\rho\mid\sigma)&=H_{\min}(\tau_3\mid\sigma),&H_{\max}^{\epsilon}(\rho\mid\sigma)&=H_{\max}(\tau_4\mid\sigma),\\
--   H_{\min}^{\epsilon}(\rho\mid B)&=H_{\min}^{\epsilon}(\rho\mid s_5),&H_{\max}^{\epsilon}(\rho\mid B)&=H_{\max}^{\epsilon}(\rho\mid s_6).
--   \end{aligned}
--   $$
--
--   This pins the source’s attainment remark to its six actual entropy optimizations, rather than arbitrary subsets of a finite-dimensional space.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 15, Remark 3.18

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P11

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Support50.P21
  (conditionalMin conditionalMax hMin hMax largestEigenvalue)

open QAlgorithms.Papers.Independent.Dependency50.P35 (elog supportRank tr)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC marginalAR)

open QAlgorithms.Papers.Independent.Information100.P22 (bell mixed)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Remark 3.18, PDF p.15: actual attainment of the six optimizations in
(3.5),(3.6),(3.32)--(3.35). This is not a generic assertion that every supremum in
finite dimension is attained. All states in the smoothing ball are normalized. -/
theorem entropy_optimizations_attained {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (sigma : Matrix B B ℂ) (hsigma : IsDensityMatrix sigma) (eps : ℝ) (heps : 0 ≤ eps) :
    (∃ s : Matrix B B ℂ, IsDensityMatrix s ∧ optimizedMin rho = conditionalMin rho s) ∧
    (∃ s : Matrix B B ℂ, IsDensityMatrix s ∧ optimizedMax rho = conditionalMax rho s) ∧
    (∃ tau ∈ normalizedBall eps rho, normalizedSmoothFixedMin eps rho sigma = conditionalMin tau sigma) ∧
    (∃ tau ∈ normalizedBall eps rho, smoothFixedMax eps rho sigma = conditionalMax tau sigma) ∧
    (∃ s : Matrix B B ℂ, IsDensityMatrix s ∧ normalizedSmoothMin eps rho = normalizedSmoothFixedMin eps rho s) ∧
    (∃ s : Matrix B B ℂ, IsDensityMatrix s ∧ normalizedSmoothRankMax eps rho = smoothFixedMax eps rho s) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end
