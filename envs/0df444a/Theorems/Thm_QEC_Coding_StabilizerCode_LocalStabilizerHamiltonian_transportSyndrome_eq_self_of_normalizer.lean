-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_transportSyndrome_eq_self_of_normalizer
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.transportSyndrome_eq_self_of_normalizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:37.906197+00:00
-- url     : https://prove2.me/theorems/c81dabbe-8334-46f1-bf63-cd69ea585d66
-- title:
--   Local Stabilizer Hamiltonian: transport Syndrome eq self of normalizer
-- statement:
--   A normalizer Pauli leaves every selected joint syndrome unchanged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L219-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L219-L226

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
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.transportSyndrome_eq_self_of_normalizer
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    {logical : Binary ι} (hlogical : H.code.1.InBinaryNormalizer logical)
    (syndrome : DecoderSyndrome κ) :
    H.transportSyndrome logical syndrome = syndrome := by sorry
