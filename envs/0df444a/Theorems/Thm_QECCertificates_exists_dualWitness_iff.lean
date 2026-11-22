-- Prove2me | Theorems.Thm_QECCertificates_exists_dualWitness_iff
-- name    : QECCertificates.exists_dualWitness_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:21.245796+00:00
-- url     : https://prove2.me/theorems/400285ab-5350-4bf7-9d3d-dd9e7d447031
-- title:
--   QECCertificates: exists dual Witness iff
-- statement:
--   **Certificate completeness**: `E` is not in the row space if and only if a dual
--   witness exists.
--
--   Completeness is LeanQEC's `not_mem_rowspace_iff_exists_mem_ker`; this package wraps its
--   existential output in the shape of a checkable certificate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Witness.lean#L99-L105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Witness.lean#L99-L105

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.exists_dualWitness_iff {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) (E : Vec n) :
    (∃ _ : DualWitness H E, True) ↔ E ∉ H.certificateRowSpace := by sorry
