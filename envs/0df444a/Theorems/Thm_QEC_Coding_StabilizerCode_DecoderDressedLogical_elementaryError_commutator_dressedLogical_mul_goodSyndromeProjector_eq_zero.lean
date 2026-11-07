-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_elementaryError_commutator_dressedLogical_mul_goodSyndromeProjector_eq_zero
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.elementaryError_commutator_dressedLogical_mul_goodSyndromeProjector_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:14:48.251204+00:00
-- url     : https://prove2.me/theorems/f368c58a-ab01-4150-b63c-7f6394f3a5c6
-- title:
--   Decoder Dressed Logical: elementary Error commutator dressed Logical mul good Syndrome Projector eq zero
-- statement:
--   For every selected elementary error, the dressed normalizer commutator
--   vanishes after restriction to `P_good`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L486-L505
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L486-L505

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.elementaryError_commutator_dressedLogical_mul_goodSyndromeProjector_eq_zero
    (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι))
    {error : Binary ι} (herror : error ∈ elementaryErrors)
    {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical) :
    (toHermitianQubitOperator error * D.dressedLogical logical -
        D.dressedLogical logical * toHermitianQubitOperator error) *
      D.goodSyndromeProjector elementaryErrors = 0 := by sorry
