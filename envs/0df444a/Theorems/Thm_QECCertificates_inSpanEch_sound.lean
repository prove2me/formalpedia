-- Prove2me | Theorems.Thm_QECCertificates_inSpanEch_sound
-- name    : QECCertificates.inSpanEch_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:08.524313+00:00
-- url     : https://prove2.me/theorems/f2dd6771-52a5-48f1-97c2-1bd7642f3b78
-- title:
--   QECCertificates: in Span Ech sound
-- statement:
--   The QECCertificates construction uses the in Span Ech sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L472-L479
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L472-L479

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.inSpanEch_sound {L : List (Vec n)} {v : Vec n} (h : inSpanEch L v = true) :
    v ∈ spanL L := by sorry
