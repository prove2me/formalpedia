-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorTwoThirdsSeparationProfile_eq_measured
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorTwoThirdsSeparationProfile_eq_measured
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:08:07.012443+00:00
-- url     : https://prove2.me/theorems/bd846027-81db-44cb-bb2d-8cf31f73bd49
-- title:
--   Binary Stabilizer Presentation: fixed Generator Two Thirds Separation Profile eq measured
-- statement:
--   The fixed-generator profile is the measured finite maximum, not an input bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Core.lean#L293-L297
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Core.lean#L293-L297

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorTwoThirdsSeparationProfile_eq_measured
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (scale : Nat) :
    P.fixedGeneratorTwoThirdsSeparationProfile scale =
      Locality.twoThirdsSeparationProfile P.fixedGeneratorInteractionGraph scale := by sorry
