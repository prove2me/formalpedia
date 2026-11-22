-- Prove2me | Theorems.Thm_QECCertificates_sum_ite_self
-- name    : QECCertificates.sum_ite_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:06.83445+00:00
-- url     : https://prove2.me/theorems/bd0b53b9-abcf-44e2-a3e1-7e40468643f6
-- title:
--   QECCertificates: sum ite self
-- statement:
--   `∑ i, (if i = a then u i else 0) = u a`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L81-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L81-L87

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.sum_ite_self (u : Vec n) (a : Fin n) :
    ∑ i, (if i = a then u i else 0) = u a := by sorry
