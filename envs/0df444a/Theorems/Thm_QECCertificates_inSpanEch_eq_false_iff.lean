-- Prove2me | Theorems.Thm_QECCertificates_inSpanEch_eq_false_iff
-- name    : QECCertificates.inSpanEch_eq_false_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:39.710794+00:00
-- url     : https://prove2.me/theorems/6e8e0887-3eb8-4c2c-afcb-ee8bb6305d8e
-- title:
--   QECCertificates: in Span Ech eq false iff
-- statement:
--   **Negative form (echelon backend)**: consumed on the lower-bound side.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L575-L584
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L575-L584

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.inSpanEch_eq_false_iff (L : List (Vec n)) (v : Vec n) :
    inSpanEch L v = false ↔ v ∉ spanL L := by sorry
