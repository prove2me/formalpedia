-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_constantCoeff_eq_zero_of_isProjPrime_3532aee1cba7
-- name    : P2M_GroundTheory_Heights__Heights_constantCoeff_eq_zero_of_isProjPrime_3532aee1cba7
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:45:06.740414+00:00
-- url     : https://prove2.me/theorems/31258130-c57b-4f4f-8b05-4dfdc13ccc80
-- title:
--   P2 M Ground Theory Heights  Heights constant Coeff eq zero of is Proj Prime 3532aee1cba7: P2 M Ground Theory Heights  Heights constant Coeff eq zero of is Proj Prime 3532aee1cba7
-- statement:
--   The P2 M Ground Theory Heights  Heights constant Coeff eq zero of is Proj Prime 3532aee1cba7 construction uses the P2 M Ground Theory Heights  Heights constant Coeff eq zero of is Proj Prime 3532aee1cba7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChowFormExists.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChowFormExists.lean#L10-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormExists
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

theorem P2M_GroundTheory_Heights__Heights_constantCoeff_eq_zero_of_isProjPrime_3532aee1cba7 {F : Type*} [Field F] {n : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P) {f : MvPolynomial (Fin n) F}
    (hf : f ∈ P) : constantCoeff f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«constantCoeff_eq_zero_of_isProjPrime» := P2M_GroundTheory_Heights__Heights_constantCoeff_eq_zero_of_isProjPrime_3532aee1cba7
