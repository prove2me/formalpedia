-- Prove2me | Theorems.Thm_PI_DivPowInteg_Gen_gdelta_mem_lowDeg_inl
-- name    : PI.DivPowInteg.Gen.gdelta_mem_lowDeg_inl
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:01.572949+00:00
-- url     : https://prove2.me/theorems/cc9de369-95eb-43ff-87b3-a15ecfba5afd
-- title:
--   Gen: gdelta mem low Deg inl
-- statement:
--   The Gen construction uses the gdelta mem low Deg inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/DividedPowerIntegrals/GenVan.lean#L86-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/DividedPowerIntegrals/GenVan.lean#L86-L91

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
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]

theorem PI.DivPowInteg.Gen.gdelta_mem_lowDeg_inl (κ : I → J → K) {t : ℕ} {R : MvPolynomial (I ⊕ J) K}
    (h : R ∈ lowDeg (Sum.inl : I → I ⊕ J) (t + 1)) :
    gdelta κ R ∈ lowDeg (Sum.inl : I → I ⊕ J) t := by sorry
