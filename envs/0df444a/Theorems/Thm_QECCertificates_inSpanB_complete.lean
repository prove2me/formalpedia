-- Prove2me | Theorems.Thm_QECCertificates_inSpanB_complete
-- name    : QECCertificates.inSpanB_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:26.491077+00:00
-- url     : https://prove2.me/theorems/dc0c6a13-e565-4675-9bdc-4a4a5f62a703
-- title:
--   QECCertificates: in Span B complete
-- statement:
--   **Completeness**: if `v` lies in the row space then `inSpanB` reports true.
--
--   Immediate from `reduceAgainst_eq_zero_of_mem_spanL`, together with invariance of the row
--   space.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Membership.lean#L173-L177
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Membership.lean#L173-L177

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

theorem QECCertificates.inSpanB_complete {L : List (Vec n)} {v : Vec n} (hv : v ∈ spanL L) :
    inSpanB L v = true := by sorry
