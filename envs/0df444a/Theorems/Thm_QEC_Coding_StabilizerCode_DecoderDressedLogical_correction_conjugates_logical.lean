-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_correction_conjugates_logical
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.correction_conjugates_logical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:16:42.344023+00:00
-- url     : https://prove2.me/theorems/0f37cf0e-fcc7-4479-8bf6-b4079d276ae3
-- title:
--   Decoder Dressed Logical: correction conjugates logical
-- statement:
--   The phase is exactly the source conjugation coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L282-L322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L282-L322

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.correction_conjugates_logical
    (D : DecoderDressedLogical H) (logical : Binary ι)
    (syndrome : DecoderSyndrome κ) :
    LinearMap.adjoint (toHermitianQubitOperator (D.correction syndrome)) *
          toHermitianQubitOperator logical *
        toHermitianQubitOperator (D.correction syndrome) =
      D.phase logical syndrome • toHermitianQubitOperator logical := by sorry
