-- Prove2me | Theorems.Thm_QECCertificates_mem_kerBasis
-- name    : QECCertificates.mem_kerBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:45:31.667641+00:00
-- url     : https://prove2.me/theorems/77980e61-3093-4e62-811c-be444329a634
-- title:
--   QECCertificates: mem ker Basis
-- statement:
--   The QECCertificates construction uses the mem ker Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L267-L274
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L267-L274

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.mem_kerBasis {D : List (PivRow n)} {x : Vec n} :
    x ∈ kerBasis D ↔ ∃ j, j ∉ pivCols D ∧ kerVec D j = x := by sorry
