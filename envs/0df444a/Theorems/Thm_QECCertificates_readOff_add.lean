-- Prove2me | Theorems.Thm_QECCertificates_readOff_add
-- name    : QECCertificates.readOff_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:41.437719+00:00
-- url     : https://prove2.me/theorems/b46079d1-4583-42e2-866e-ff4c15bb5458
-- title:
--   QECCertificates: read Off add
-- statement:
--   The QECCertificates construction uses the read Off add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L78-L82
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L78-L82

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.readOff_add (D : List (PivRow n)) (x y : Vec n) :
    readOff D (x + y) = readOff D x + readOff D y := by sorry
