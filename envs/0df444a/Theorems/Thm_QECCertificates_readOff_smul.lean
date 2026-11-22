-- Prove2me | Theorems.Thm_QECCertificates_readOff_smul
-- name    : QECCertificates.readOff_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:42.180521+00:00
-- url     : https://prove2.me/theorems/67c18522-fb58-4f95-9f25-e34a9077c980
-- title:
--   QECCertificates: read Off smul
-- statement:
--   The QECCertificates construction uses the read Off smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L84-L89
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L84-L89

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.readOff_smul (D : List (PivRow n)) (c : ZMod 2) (x : Vec n) :
    readOff D (c • x) = c • readOff D x := by sorry
