-- Prove2me | Theorems.Thm_QECCertificates_rowReduce_mem_iff_of_spanL_eq
-- name    : QECCertificates.rowReduce_mem_iff_of_spanL_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:05:19.420653+00:00
-- url     : https://prove2.me/theorems/c784c1bc-2573-4d00-a79f-bf3959db17b3
-- title:
--   QECCertificates: row Reduce mem iff of span L eq
-- statement:
--   **Canonical invariance (main theorem)**: two row lists with the same row space have the same set
--   of rows after elimination.
--
--   This is the **decidable criterion**, inside the kernel, for whether two codes are the same: compare
--   the row sets of their elimination outputs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L351-L354
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L351-L354

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.rowReduce_mem_iff_of_spanL_eq {L₁ L₂ : List (Vec n)} (h : spanL L₁ = spanL L₂)
    (x : PivRow n) : x ∈ rowReduce L₁ ↔ x ∈ rowReduce L₂ := by sorry
