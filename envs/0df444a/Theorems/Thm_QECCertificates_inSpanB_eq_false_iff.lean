-- Prove2me | Theorems.Thm_QECCertificates_inSpanB_eq_false_iff
-- name    : QECCertificates.inSpanB_eq_false_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:28.796428+00:00
-- url     : https://prove2.me/theorems/994a5b6a-493f-4335-9f5a-fb57b6607cbf
-- title:
--   QECCertificates: in Span B eq false iff
-- statement:
--   **Semantic equivalence, negative form** (consumed on the lower-bound side): reports
--   false exactly when the vector is not in the row space.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Membership.lean#L191-L200
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Membership.lean#L191-L200

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.inSpanB_eq_false_iff (L : List (Vec n)) (v : Vec n) :
    inSpanB L v = false ↔ v ∉ spanL L := by sorry
