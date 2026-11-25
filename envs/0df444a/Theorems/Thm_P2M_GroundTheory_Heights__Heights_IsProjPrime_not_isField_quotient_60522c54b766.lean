-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsProjPrime_not_isField_quotient_60522c54b766
-- name    : P2M_GroundTheory_Heights__Heights_IsProjPrime_not_isField_quotient_60522c54b766
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:45:18.411482+00:00
-- url     : https://prove2.me/theorems/a4de726b-8921-46cd-8e2e-a257a7bd5ca4
-- title:
--   P2 M Ground Theory Heights  Heights Is Proj Prime not is Field quotient 60522c54b766: P2 M Ground Theory Heights  Heights Is Proj Prime not is Field quotient 60522c54b766
-- statement:
--   The P2 M Ground Theory Heights  Heights Is Proj Prime not is Field quotient 60522c54b766 construction uses the P2 M Ground Theory Heights  Heights Is Proj Prime not is Field quotient 60522c54b766 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PConeDimOfChowForm.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PConeDimOfChowForm.lean#L25-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PConeDimOfChowForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_IsProjPrime_not_isField_quotient_60522c54b766 {F : Type*} [Field F] {n : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P) :
    ¬ IsField (MvPolynomial (Fin n) F ⧸ P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsProjPrime».«not_isField_quotient» := P2M_GroundTheory_Heights__Heights_IsProjPrime_not_isField_quotient_60522c54b766
