-- Prove2me | Theorems.Thm_PI_DivPowInteg_Gen_pow_apply_eq_zero_of_lowDeg
-- name    : PI.DivPowInteg.Gen.pow_apply_eq_zero_of_lowDeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:21.594704+00:00
-- url     : https://prove2.me/theorems/898a8931-f803-432a-85f2-e38c10fa3d48
-- title:
--   Gen: pow apply eq zero of low Deg
-- statement:
--   The Gen construction uses the pow apply eq zero of low Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/DividedPowerIntegrals/GenVan.lean#L63-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/DividedPowerIntegrals/GenVan.lean#L63-L75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenVan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.DivPowInteg PI.DivPowInteg.Gen
variable {K σ ι : Type} [CommRing K] [Fintype ι]

theorem PI.DivPowInteg.Gen.pow_apply_eq_zero_of_lowDeg (D : Module.End K (MvPolynomial σ K)) (f : ι → σ)
    (hD : ∀ t R, R ∈ lowDeg f (t + 1) → D R ∈ lowDeg f t) :
    ∀ n R, R ∈ lowDeg f n → (D ^ n) R = 0 := by sorry
