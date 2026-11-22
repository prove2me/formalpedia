-- Prove2me | Theorems.Thm_QECCertificates_leadIdx_eq_piv_of_isEchelon
-- name    : QECCertificates.leadIdx_eq_piv_of_isEchelon
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:48.033079+00:00
-- url     : https://prove2.me/theorems/c61a2063-65d1-49fe-b477-a62906b2cd10
-- title:
--   QECCertificates: lead Idx eq piv of is Echelon
-- statement:
--   The pivot column of an echelon row list is the `leadIdx` of its row.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L156-L161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L156-L161

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.leadIdx_eq_piv_of_isEchelon {D : List (PivRow n)} (h : IsEchelon D) {ri : PivRow n}
    (hri : ri ∈ D) {hne : ri.1 ≠ 0} : leadIdx ri.1 hne = ri.2 := by sorry
