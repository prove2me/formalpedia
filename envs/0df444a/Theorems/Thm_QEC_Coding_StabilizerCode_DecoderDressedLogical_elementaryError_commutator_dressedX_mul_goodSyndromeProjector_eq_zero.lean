-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_elementaryError_commutator_dressedX_mul_goodSyndromeProjector_eq_zero
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.elementaryError_commutator_dressedX_mul_goodSyndromeProjector_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:46.222755+00:00
-- url     : https://prove2.me/theorems/791f45a8-7d94-441a-8506-e1396654e46e
-- title:
--   Decoder Dressed Logical: elementary Error commutator dressed X mul good Syndrome Projector eq zero
-- statement:
--   Every selected elementary error protects the dressed logical `X`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L508-L516
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L508-L516

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.elementaryError_commutator_dressedX_mul_goodSyndromeProjector_eq_zero
    (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι))
    {error : Binary ι} (herror : error ∈ elementaryErrors) :
    (toHermitianQubitOperator error * D.dressedX -
        D.dressedX * toHermitianQubitOperator error) *
      D.goodSyndromeProjector elementaryErrors = 0 := by sorry
