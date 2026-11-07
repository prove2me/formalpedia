-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndrome_phase_transport
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndrome_phase_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:17:34.660829+00:00
-- url     : https://prove2.me/theorems/f56de2b1-6672-494b-b523-66cc40851c32
-- title:
--   Decoder Dressed Logical: good Syndrome phase transport
-- statement:
--   Goodness forces the decoder phase after an elementary error to equal the old
--   decoder phase times that error's commutation sign with the logical Pauli.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L115-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L115-L174

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndrome_phase_transport
    (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι))
    {syndrome : DecoderSyndrome κ}
    (hgood : D.goodSyndrome elementaryErrors syndrome)
    {error : Binary ι} (herror : error ∈ elementaryErrors)
    {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical) :
    D.phase logical (H.transportSyndrome error syndrome) =
      commutationPhase error logical * D.phase logical syndrome := by sorry
