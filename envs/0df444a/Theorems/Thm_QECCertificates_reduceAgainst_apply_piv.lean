-- Prove2me | Theorems.Thm_QECCertificates_reduceAgainst_apply_piv
-- name    : QECCertificates.reduceAgainst_apply_piv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:44:31.925068+00:00
-- url     : https://prove2.me/theorems/43fe1073-7da0-414f-83ea-2b69e8344907
-- title:
--   QECCertificates: reduce Against apply piv
-- statement:
--   **Core lemma**: when `D` is mutually reduced, the reduced vector is 0 at every pivot column.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L105-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L105-L127

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.reduceAgainst_apply_piv {D : List (PivRow n)} (hD : IsReduced D) (v : Vec n) :
    ∀ ri ∈ D, reduceAgainst D v ri.2 = 0 := by sorry
