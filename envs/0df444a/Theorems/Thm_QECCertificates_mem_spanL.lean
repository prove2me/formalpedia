-- Prove2me | Theorems.Thm_QECCertificates_mem_spanL
-- name    : QECCertificates.mem_spanL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:49.533616+00:00
-- url     : https://prove2.me/theorems/73a2e618-2ebc-40fe-a332-c7c677289bde
-- title:
--   QECCertificates: mem span L
-- statement:
--   The QECCertificates construction uses the mem span L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L105-L106
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L105-L106

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.mem_spanL {L : List (Vec n)} {x : Vec n} :
    x ∈ spanL L ↔ x ∈ Submodule.span (ZMod 2) {y | y ∈ L} := by sorry
