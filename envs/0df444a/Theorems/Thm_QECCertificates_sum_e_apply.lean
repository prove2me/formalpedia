-- Prove2me | Theorems.Thm_QECCertificates_sum_e_apply
-- name    : QECCertificates.sum_e_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:52.477454+00:00
-- url     : https://prove2.me/theorems/d361258e-99c9-451d-96b3-dce432b79dd8
-- title:
--   QECCertificates: sum e apply
-- statement:
--   **Evaluating a basis-vector sum on a duplicate-free support**: a coordinate is `1`
--   exactly when it lies on the support.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basis.lean#L65-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basis.lean#L65-L76

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.sum_e_apply (l : List (Fin n)) (h : l.Nodup) (a : Fin n) :
    ((l.map e).sum : Vec n) a = if a ∈ l then 1 else 0 := by sorry
