-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_generatorOperator_commute_phaseOperator
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.generatorOperator_commute_phaseOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:16:57.769475+00:00
-- url     : https://prove2.me/theorems/12a1617a-e271-4074-8e1d-1cfbd7bd6418
-- title:
--   Decoder Dressed Logical: generator Operator commute phase Operator
-- statement:
--   Every decoder phase operator commutes with every selected generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L593-L603
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L593-L603

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
open Semantics
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
open QEC.Coding.StabilizerCode.DecoderDressedLogical
variable {H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)}

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.generatorOperator_commute_phaseOperator
    (D : DecoderDressedLogical H) (check : κ) (logical : Binary ι) :
    Commute (H.generatorOperator check) (D.phaseOperator logical) := by sorry
