-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_syndromeProjector_commute_dressedLogical
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.syndromeProjector_commute_dressedLogical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:14.218191+00:00
-- url     : https://prove2.me/theorems/9f02e5ba-6a17-4f8f-9749-15b66c444063
-- title:
--   Decoder Dressed Logical: syndrome Projector commute dressed Logical
-- statement:
--   Every syndrome sector is invariant under a dressed normalizer Pauli.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L296-L323
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L296-L323

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.syndromeProjector_commute_dressedLogical
    (D : DecoderDressedLogical H) {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical)
    (syndrome : DecoderSyndrome κ) :
    Commute (H.syndromeProjector syndrome) (D.dressedLogical logical) := by sorry
