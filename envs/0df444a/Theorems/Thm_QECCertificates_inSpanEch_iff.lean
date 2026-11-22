-- Prove2me | Theorems.Thm_QECCertificates_inSpanEch_iff
-- name    : QECCertificates.inSpanEch_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:08.738299+00:00
-- url     : https://prove2.me/theorems/f4d94e62-c450-473b-82d4-7639255a8581
-- title:
--   QECCertificates: in Span Ech iff
-- statement:
--   **Semantic equivalence of the membership test (echelon backend)**: the same Boolean
--   value as `inSpanB`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L489-L491
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L489-L491

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.inSpanEch_iff (L : List (Vec n)) (v : Vec n) :
    inSpanEch L v = true ↔ v ∈ spanL L := by sorry
