-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_smoothMin_reference_support
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.smoothMin_reference_support
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:43:16.20596+00:00
-- url     : https://prove2.me/theorems/0722d22d-f9b6-4c2e-b30b-92d7eca88589
-- title:
--   Restrict the outer smooth-min reference supremum
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. Here $H_{\min}(\rho_{AB}\mid\sigma_B)$ is the fixed-reference min entropy, and $H_{\max}(\rho_{AB}\mid\sigma_B)$ is the historical support-rank max entropy, $\log_2\operatorname{tr}[(I_A\otimes\sigma_B)\Pi_{\rho_{AB}}]$, where $\Pi_\rho$ is the support projector. A conditioning register in place of a reference density means a supremum over normalized reference densities. The superscript $\epsilon$ denotes optimization over normalized density operators at half trace-norm distance at most $\epsilon$: a supremum for fixed-reference min entropy and an infimum for fixed-reference rank-max entropy, followed by a supremum over normalized reference densities when conditioning on a register. Let $\rho_{AB}$ be a density operator and $\epsilon\ge0$. Then
--
--   $$
--   H_{\min}^{\epsilon}(\rho_{AB}\mid B)=
--   \sup_{\substack{\sigma_B\text{ density}\\ \operatorname{supp}\rho_B\subseteq\operatorname{supp}\sigma_B}}
--   H_{\min}^{\epsilon}(\rho_{AB}\mid\sigma_B),
--   $$
--
--   where $\rho_B=\operatorname{tr}_A\rho_{AB}$ is the original marginal, before smoothing. The inner normalized state optimization is unchanged.
--
--   Only the reference optimization is restricted; smoothing does not redefine the support condition.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 14, Remark 3.14

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

/-- Remark 3.14, PDF p.14: restrict only the OUTER reference supremum, using the ORIGINAL marginal. -/
theorem smoothMin_reference_support {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (eps : ℝ) (heps : 0 ≤ eps) :
    normalizedSmoothMin eps rho =
      ⨆ sigma : {s : Matrix B B ℂ // IsDensityMatrix s ∧ SupportIncluded (traceLeft rho) s},
        normalizedSmoothFixedMin eps rho sigma.1 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end
