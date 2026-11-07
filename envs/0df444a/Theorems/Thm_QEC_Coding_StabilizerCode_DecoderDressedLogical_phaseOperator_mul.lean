-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_phaseOperator_mul
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.phaseOperator_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:14:30.403201+00:00
-- url     : https://prove2.me/theorems/8e66f060-6f5d-4c61-afd9-2f31b4ed6dbc
-- title:
--   Decoder Dressed Logical: phase Operator mul
-- statement:
--   Multiplication of decoder phase operators is pointwise on syndrome sectors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L342-L358
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L342-L358

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.phaseOperator_mul
    (D : DecoderDressedLogical H) (left right : Binary ι) :
    D.phaseOperator left * D.phaseOperator right =
      ∑ syndrome : DecoderSyndrome κ,
        (D.phase left syndrome * D.phase right syndrome) •
          H.syndromeProjector syndrome := by sorry
