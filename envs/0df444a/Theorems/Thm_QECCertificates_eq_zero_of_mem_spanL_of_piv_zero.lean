-- Prove2me | Theorems.Thm_QECCertificates_eq_zero_of_mem_spanL_of_piv_zero
-- name    : QECCertificates.eq_zero_of_mem_spanL_of_piv_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:23.507979+00:00
-- url     : https://prove2.me/theorems/abcdcbf8-49e1-474c-a769-e1be357fc66f
-- title:
--   QECCertificates: eq zero of mem span L of piv zero
-- statement:
--   **The vanishing lemma**: an element of the row space that takes the value zero on every pivot
--   column is the zero vector.
--   (A corollary of the read-off, and the direct form of "the values on the pivot columns determine
--   everything".)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L123-L128
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L123-L128

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.eq_zero_of_mem_spanL_of_piv_zero {D : List (PivRow n)} (hD : IsReduced D) {w : Vec n}
    (hw : w ∈ spanL (rowList D)) (h0 : ∀ ri ∈ D, w ri.2 = 0) : w = 0 := by sorry
