-- Prove2me | Theorems.Thm_QECCertificates_eq_sum_of_piv_support
-- name    : QECCertificates.eq_sum_of_piv_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:00.748986+00:00
-- url     : https://prove2.me/theorems/067a8844-0356-4253-98f7-272072b1f884
-- title:
--   QECCertificates: eq sum of piv support
-- statement:
--   A vector supported on the pivot columns is recovered from the pivot columns.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L279-L301
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L279-L301

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.eq_sum_of_piv_support {D : List (PivRow n)} (hD : IsReduced D) {z : Vec n}
    (hz : ∀ i, (∀ ri ∈ D, ri.2 ≠ i) → z i = 0) :
    ∀ m, z m = ∑ rl ∈ D.toFinset, (if rl.2 = m then z rl.2 else 0) := by sorry
