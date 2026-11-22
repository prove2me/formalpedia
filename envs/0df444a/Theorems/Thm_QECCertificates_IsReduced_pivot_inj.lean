-- Prove2me | Theorems.Thm_QECCertificates_IsReduced_pivot_inj
-- name    : QECCertificates.IsReduced.pivot_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:44:33.293768+00:00
-- url     : https://prove2.me/theorems/43b55874-6674-4625-b947-8043097f730f
-- title:
--   Is Reduced: pivot inj
-- statement:
--   Immediate consequence of (R2): the pivot columns are pairwise distinct.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L67-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L67-L75

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.IsReduced.pivot_inj {D : List (PivRow n)} (h : IsReduced D) :
    ∀ ri ∈ D, ∀ rj ∈ D, ri.2 = rj.2 → ri = rj := by sorry
