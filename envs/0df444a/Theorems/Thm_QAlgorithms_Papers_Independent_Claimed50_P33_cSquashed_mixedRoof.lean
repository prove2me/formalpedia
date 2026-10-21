-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_cSquashed_mixedRoof
-- name    : QAlgorithms.Papers.Independent.Claimed50.P33.cSquashed_mixedRoof
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:42:39.575388+00:00
-- url     : https://prove2.me/theorems/565539c6-d370-43d2-85cb-a15f3fb40a68
-- title:
--   §IV.E: c-squashed equals the mixed roof, for I and S
-- statement:
--   For $m\ge2$, let $F$ be total correlation $I_m$ or dual correlation $S_m$, in bits. Let $E_F^c$ be the infimum of the conditional information over all normalized classical-on-environment extensions and all positive finite environment dimensions, without $1/2$. Then
--
--   $$E_F^c(\rho)=\inf_{\rho=\sum_i p_i\rho_i}\sum_i p_i F(\rho_i).$$
--
--   The infimum uses every finite mixed-state decomposition, with no fixed ensemble length or optimizer. Both resulting functionals are monotone on average under adaptive LOCC. Thus classical squashing is precisely a mixed convex roof.
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, PDF p. 7, §IV.E: c-squashed equals the mixed roof, for I and S

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section IV.E, PDF p.7: both c-squashed versions equal the corresponding
mixed roof, and both are average LOCC monotones. -/
theorem cSquashed_mixedRoof (m : ℕ) (hm : 2 ≤ m) : ∀ kind : InformationKind,
    (∀ s : FiniteState m,
      squashedFunctional true kind s = bundledMixedRoof (informationFunctional kind) s) ∧
    IsAdaptiveLOCCMonotone (squashedFunctional true kind : FiniteState m → ℝ) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P33

end
