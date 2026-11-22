-- Prove2me | Theorems.Thm_QECCertificates_addSmul_apply
-- name    : QECCertificates.addSmul_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:41:53.948907+00:00
-- url     : https://prove2.me/theorems/13639237-542c-41c5-b425-2e1f709bdc0d
-- title:
--   QECCertificates: add Smul apply
-- statement:
--   The QECCertificates construction uses the add Smul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L210-L212
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L210-L212

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.addSmul_apply (v r : Vec n) (c : ZMod 2) (i : Fin n) :
    addSmul v r c i = v i + c * r i := by sorry
