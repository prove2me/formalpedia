-- Prove2me | Theorems.Thm_QECCertificates_addSmul_zero_coord
-- name    : QECCertificates.addSmul_zero_coord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:44.56023+00:00
-- url     : https://prove2.me/theorems/e41738b0-65a9-4432-b710-e62acfb1d00b
-- title:
--   QECCertificates: add Smul zero coord
-- statement:
--   With `c = v i` and `r i = 1`, the operation clears the `i`-th coordinate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L215-L218
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L215-L218

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.addSmul_zero_coord (v r : Vec n) (i : Fin n) (hr : r i = 1) :
    addSmul v r (v i) i = 0 := by sorry
