-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_logical_commute_generatorOperator
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.logical_commute_generatorOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:16:32.565198+00:00
-- url     : https://prove2.me/theorems/f39da3f8-cce5-4b49-a61d-9f0c591b57eb
-- title:
--   Decoder Dressed Logical: logical commute generator Operator
-- statement:
--   A bare logical normalizer Pauli commutes with every selected generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L553-L563
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L553-L563

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.logical_commute_generatorOperator
    (_D : DecoderDressedLogical H) {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical) (check : κ) :
    Commute (toHermitianQubitOperator logical) (H.generatorOperator check) := by sorry
