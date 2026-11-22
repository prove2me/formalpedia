-- Prove2me | Theorems.Thm_QECCertificates_kerVec_apply
-- name    : QECCertificates.kerVec_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:45:29.593795+00:00
-- url     : https://prove2.me/theorems/260cf6f0-481c-43f5-b8d3-b913c54d9a52
-- title:
--   QECCertificates: ker Vec apply
-- statement:
--   The QECCertificates construction uses the ker Vec apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L152-L154
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L152-L154

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.kerVec_apply (D : List (PivRow n)) (j i : Fin n) :
    kerVec D j i
      = (if i = j then 1 else 0) + ∑ ri ∈ D.toFinset, (if ri.2 = i then ri.1 j else 0) := by sorry
