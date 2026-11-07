-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_card_movingFrontier_le
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.card_movingFrontier_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:16:55.771093+00:00
-- url     : https://prove2.me/theorems/2de7816d-2746-415e-83a9-418ef9df71f6
-- title:
--   Strip Geometry: card moving Frontier le
-- statement:
--   The Strip Geometry construction uses the card moving Frontier le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L492-L539
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L492-L539

import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Definitions.Def_QEC_Coding_Stabilizer_SupportEnergyBounds
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
open scoped Classical
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
open QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.card_movingFrontier_le
    (L stripStart stripWidth cursor r : Nat) :
    (movingFrontier L stripStart stripWidth cursor r).card ≤
      stripWidth * r := by sorry
