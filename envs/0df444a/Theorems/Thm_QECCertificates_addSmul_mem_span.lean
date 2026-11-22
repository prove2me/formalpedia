-- Prove2me | Theorems.Thm_QECCertificates_addSmul_mem_span
-- name    : QECCertificates.addSmul_mem_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:44.398722+00:00
-- url     : https://prove2.me/theorems/e44b79ff-08ee-4e65-bd33-ade77352f203
-- title:
--   QECCertificates: add Smul mem span
-- statement:
--   The QECCertificates construction uses the add Smul mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L226-L229
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L226-L229

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.addSmul_mem_span {S : Set (Vec n)} {v r : Vec n} (c : ZMod 2)
    (hv : v ∈ Submodule.span (ZMod 2) S) (hr : r ∈ Submodule.span (ZMod 2) S) :
    addSmul v r c ∈ Submodule.span (ZMod 2) S := by sorry
