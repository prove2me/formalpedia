-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_elementaryError_commute_dressedLogical_on_good_syndrome
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.elementaryError_commute_dressedLogical_on_good_syndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:29.822279+00:00
-- url     : https://prove2.me/theorems/0cad4787-5204-4502-af57-fb3b18322a98
-- title:
--   Decoder Dressed Logical: elementary Error commute dressed Logical on good syndrome
-- statement:
--   On one good syndrome sector, an elementary error commutes with every dressed
--   normalizer Pauli.  This is the source protection calculation before summing
--   over good sectors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L412-L480
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L412-L480

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.elementaryError_commute_dressedLogical_on_good_syndrome
    (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι))
    {syndrome : DecoderSyndrome κ}
    (hgood : D.goodSyndrome elementaryErrors syndrome)
    {error : Binary ι} (herror : error ∈ elementaryErrors)
    {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical) :
    toHermitianQubitOperator error * D.dressedLogical logical *
        H.syndromeProjector syndrome =
      D.dressedLogical logical * toHermitianQubitOperator error *
        H.syndromeProjector syndrome := by sorry
