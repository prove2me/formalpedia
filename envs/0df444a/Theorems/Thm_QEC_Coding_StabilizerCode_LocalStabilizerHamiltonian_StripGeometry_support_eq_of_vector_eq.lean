-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_support_eq_of_vector_eq
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.support_eq_of_vector_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:19:44.120832+00:00
-- url     : https://prove2.me/theorems/c6aa67a1-fc70-4414-8be2-e5d2ce403556
-- title:
--   Strip Geometry: support eq of vector eq
-- statement:
--   The Strip Geometry construction uses the support eq of vector eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L349-L353
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L349-L353

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.support_eq_of_vector_eq
    {L : Nat}
    {E F : Binary (Site L)} (hvector : E.vector = F.vector) :
    support E = support F := by sorry
