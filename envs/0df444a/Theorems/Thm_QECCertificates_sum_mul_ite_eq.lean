-- Prove2me | Theorems.Thm_QECCertificates_sum_mul_ite_eq
-- name    : QECCertificates.sum_mul_ite_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:30.405416+00:00
-- url     : https://prove2.me/theorems/460935f2-9423-43c2-8b91-6e7db55d6445
-- title:
--   QECCertificates: sum mul ite eq
-- statement:
--   `∑ i, u i * (if a = i then c else 0) = u a * c`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L72-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L72-L78

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.sum_mul_ite_eq (u : Vec n) (a : Fin n) (c : ZMod 2) :
    ∑ i, u i * (if a = i then c else 0) = u a * c := by sorry
