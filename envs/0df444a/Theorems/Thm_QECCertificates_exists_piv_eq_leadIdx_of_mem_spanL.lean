-- Prove2me | Theorems.Thm_QECCertificates_exists_piv_eq_leadIdx_of_mem_spanL
-- name    : QECCertificates.exists_piv_eq_leadIdx_of_mem_spanL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:53.484811+00:00
-- url     : https://prove2.me/theorems/f49d8df6-2162-44b4-a02b-ee337938bbdf
-- title:
--   QECCertificates: exists piv eq lead Idx of mem span L
-- statement:
--   **Main lemma (pivot characterisation)**: in the row space spanned by an echelon row list, the
--   first non-zero column of any non-zero element is one of the pivot columns of that list.
--
--   The characterisation uses only the row space itself, so it turns the "pivot set" into an
--   **invariant of the row space**, and canonical form uniqueness follows.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L170-L206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L170-L206

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.exists_piv_eq_leadIdx_of_mem_spanL {D : List (PivRow n)} (hD : IsEchelon D)
    {w : Vec n} (hw : w ∈ spanL (rowList D)) (hw0 : w ≠ 0) :
    ∃ ri ∈ D, ri.2 = leadIdx w hw0 := by sorry
