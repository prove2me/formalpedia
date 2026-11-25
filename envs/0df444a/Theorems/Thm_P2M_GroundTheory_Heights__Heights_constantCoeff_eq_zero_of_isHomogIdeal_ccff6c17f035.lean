-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_constantCoeff_eq_zero_of_isHomogIdeal_ccff6c17f035
-- name    : P2M_GroundTheory_Heights__Heights_constantCoeff_eq_zero_of_isHomogIdeal_ccff6c17f035
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:45:25.473289+00:00
-- url     : https://prove2.me/theorems/0af2e3f2-69f0-45dc-875f-a614edba0b27
-- title:
--   P2 M Ground Theory Heights  Heights constant Coeff eq zero of is Homog Ideal ccff6c17f035: P2 M Ground Theory Heights  Heights constant Coeff eq zero of is Homog Ideal ccff6c17f035
-- statement:
--   The P2 M Ground Theory Heights  Heights constant Coeff eq zero of is Homog Ideal ccff6c17f035 construction uses the P2 M Ground Theory Heights  Heights constant Coeff eq zero of is Homog Ideal ccff6c17f035 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PConeDimOfChowForm.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PConeDimOfChowForm.lean#L17-L23

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

theorem P2M_GroundTheory_Heights__Heights_constantCoeff_eq_zero_of_isHomogIdeal_ccff6c17f035 {F : Type*} [Field F] {n : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsHomogIdeal P) (htop : P ≠ ⊤)
    {g : MvPolynomial (Fin n) F} (hg : g ∈ P) : constantCoeff g = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«constantCoeff_eq_zero_of_isHomogIdeal» := P2M_GroundTheory_Heights__Heights_constantCoeff_eq_zero_of_isHomogIdeal_ccff6c17f035
