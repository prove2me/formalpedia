-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedLogical_commute_generatorOperator
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedLogical_commute_generatorOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:17:14.315774+00:00
-- url     : https://prove2.me/theorems/82b260b4-997a-4a76-aa02-3e1b00d262d1
-- title:
--   Decoder Dressed Logical: dressed Logical commute generator Operator
-- statement:
--   Every dressed normalizer Pauli commutes with each selected generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L606-L631
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L606-L631

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedLogical_commute_generatorOperator
    (D : DecoderDressedLogical H) {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical) (check : κ) :
    Commute (D.dressedLogical logical) (H.generatorOperator check) := by sorry
