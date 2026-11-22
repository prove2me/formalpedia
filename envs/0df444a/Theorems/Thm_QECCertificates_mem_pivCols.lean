-- Prove2me | Theorems.Thm_QECCertificates_mem_pivCols
-- name    : QECCertificates.mem_pivCols
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:45:27.825824+00:00
-- url     : https://prove2.me/theorems/13fee2c1-c1ef-4d21-8492-208fde8726f7
-- title:
--   QECCertificates: mem piv Cols
-- statement:
--   The QECCertificates construction uses the mem piv Cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L132-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L132-L134

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.mem_pivCols {D : List (PivRow n)} {i : Fin n} :
    i ∈ pivCols D ↔ ∃ ri ∈ D, ri.2 = i := by sorry
