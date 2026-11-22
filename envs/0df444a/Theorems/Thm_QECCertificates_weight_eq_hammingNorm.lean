-- Prove2me | Theorems.Thm_QECCertificates_weight_eq_hammingNorm
-- name    : QECCertificates.weight_eq_hammingNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:44:39.996593+00:00
-- url     : https://prove2.me/theorems/c32807a3-c9d2-4083-a09c-e948d2aeab62
-- title:
--   QECCertificates: weight eq hamming Norm
-- statement:
--   The weight used for the code distance: the size of the support, agreeing with
--   `hammingNorm` of mathlib and LeanQEC.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L84-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L84-L85

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.weight_eq_hammingNorm (v : Vec n) : (support v).card = hammingNorm v := by sorry
