-- Prove2me | Theorems.Thm_PI_DivPowInteg_Top_dpow_zero
-- name    : PI.DivPowInteg.Top.dpow_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:27:13.958654+00:00
-- url     : https://prove2.me/theorems/5aa967c5-f65f-4e24-98c3-27a557ee548e
-- title:
--   Top: dpow zero
-- statement:
--   The Top construction uses the dpow zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/DividedPowerIntegrals/NatMulFactorialBound.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/DividedPowerIntegrals/NatMulFactorialBound.lean#L20-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DivPowInteg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_NatMulFactorialBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.DivPowInteg PI.DivPowInteg.Top
open PI.DivPowInteg.Gen
variable {A K I J : Type} [CommRing A] [CommRing K] [Algebra ℚ K] [Algebra A K]
  [Fintype I] [Fintype J]

theorem PI.DivPowInteg.Top.dpow_zero (κ : I → J → K) (R : MvPolynomial (I ⊕ J) K) : dpow κ 0 R = R := by sorry
