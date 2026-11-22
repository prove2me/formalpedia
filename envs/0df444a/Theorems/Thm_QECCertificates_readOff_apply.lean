-- Prove2me | Theorems.Thm_QECCertificates_readOff_apply
-- name    : QECCertificates.readOff_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:47.891329+00:00
-- url     : https://prove2.me/theorems/7ee0a5c9-bac8-4048-ad47-43faeb5c9e42
-- title:
--   QECCertificates: read Off apply
-- statement:
--   Componentwise form: the smul expanded into scalar multiplication.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L73-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L73-L76

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.readOff_apply (D : List (PivRow n)) (w : Vec n) (i : Fin n) :
    readOff D w i = ∑ ri ∈ D.toFinset, (w ri.2) * (ri.1 i) := by sorry
