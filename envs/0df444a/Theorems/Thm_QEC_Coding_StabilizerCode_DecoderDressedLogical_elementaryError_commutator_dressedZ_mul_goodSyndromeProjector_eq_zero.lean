-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_elementaryError_commutator_dressedZ_mul_goodSyndromeProjector_eq_zero
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.elementaryError_commutator_dressedZ_mul_goodSyndromeProjector_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:52.521398+00:00
-- url     : https://prove2.me/theorems/2643b4f4-c635-4fdd-bbeb-2de1f47f8141
-- title:
--   Decoder Dressed Logical: elementary Error commutator dressed Z mul good Syndrome Projector eq zero
-- statement:
--   Every selected elementary error protects the dressed logical `Z`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L519-L527
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L519-L527

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.elementaryError_commutator_dressedZ_mul_goodSyndromeProjector_eq_zero
    (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι))
    {error : Binary ι} (herror : error ∈ elementaryErrors) :
    (toHermitianQubitOperator error * D.dressedZ -
        D.dressedZ * toHermitianQubitOperator error) *
      D.goodSyndromeProjector elementaryErrors = 0 := by sorry
