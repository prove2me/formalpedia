-- Prove2me | Theorems.Thm_QECCertificates_eq_zero_of_piv_support
-- name    : QECCertificates.eq_zero_of_piv_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:59.753939+00:00
-- url     : https://prove2.me/theorems/7b874afa-68ae-409f-9947-79f07dd4b47d
-- title:
--   QECCertificates: eq zero of piv support
-- statement:
--   **The entries at the pivot columns determine everything**: a vector supported on the
--   pivot columns that also lies in the kernel must be zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L305-L332
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L305-L332

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.eq_zero_of_piv_support {D : List (PivRow n)} (hD : IsReduced D) {z : Vec n}
    (hz : ∀ i, (∀ ri ∈ D, ri.2 ≠ i) → z i = 0) (hzker : ∀ ri ∈ D, ri.1 ⬝ᵥ z = 0) :
    z = 0 := by sorry
