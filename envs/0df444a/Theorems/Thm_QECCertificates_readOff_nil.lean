-- Prove2me | Theorems.Thm_QECCertificates_readOff_nil
-- name    : QECCertificates.readOff_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:45:55.91059+00:00
-- url     : https://prove2.me/theorems/f03d746c-08fc-432b-a8ed-188f0dd7a9e4
-- title:
--   QECCertificates: read Off nil
-- statement:
--   The QECCertificates construction uses the read Off nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L69-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L69-L70

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.readOff_nil (w : Vec n) : readOff ([] : List (PivRow n)) w = 0 := by sorry
