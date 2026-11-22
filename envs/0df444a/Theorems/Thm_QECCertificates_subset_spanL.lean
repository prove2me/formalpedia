-- Prove2me | Theorems.Thm_QECCertificates_subset_spanL
-- name    : QECCertificates.subset_spanL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:42:00.706282+00:00
-- url     : https://prove2.me/theorems/024c1452-4e05-486a-b025-e0ffc14c4146
-- title:
--   QECCertificates: subset span L
-- statement:
--   The QECCertificates construction uses the subset span L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L108-L109
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L108-L109

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.subset_spanL {L : List (Vec n)} {x : Vec n} (h : x ∈ L) : x ∈ spanL L := by sorry
