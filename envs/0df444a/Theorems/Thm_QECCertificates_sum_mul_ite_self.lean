-- Prove2me | Theorems.Thm_QECCertificates_sum_mul_ite_self
-- name    : QECCertificates.sum_mul_ite_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:43.037438+00:00
-- url     : https://prove2.me/theorems/efbb54ce-6d83-46ee-a487-804ba0b3c6e0
-- title:
--   QECCertificates: sum mul ite self
-- statement:
--   `∑ i, u i * (if i = a then 1 else 0) = u a`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L63-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L63-L69

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.sum_mul_ite_self (u : Vec n) (a : Fin n) :
    ∑ i, u i * (if i = a then (1 : ZMod 2) else 0) = u a := by sorry
