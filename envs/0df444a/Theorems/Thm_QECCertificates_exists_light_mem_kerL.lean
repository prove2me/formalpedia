-- Prove2me | Theorems.Thm_QECCertificates_exists_light_mem_kerL
-- name    : QECCertificates.exists_light_mem_kerL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:07.716103+00:00
-- url     : https://prove2.me/theorems/d1e50bad-96f7-470d-9c8b-57afe6425cd1
-- title:
--   QECCertificates: exists light mem ker L
-- statement:
--   **The row-list form of the frontier-argument step**: as long as `rowReduce L` still
--   has a free column, that is, as long as the kernel is nontrivial, the kernel of `L` contains
--   a nonzero element of weight $\le 1+\#(rowReduce L)$.
--
--   Now $\#(rowReduce L)$ is the rank of `L`, so this is the full statement that a matrix of
--   rank $\rho$ has a nonzero kernel vector of weight $\le\rho+1$: existence comes from the
--   completeness direction of `kerL_rowReduce`, while nonzeroness and the weight bound come
--   from the two results above.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L409-L416
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L409-L416

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.exists_light_mem_kerL (L : List (Vec n)) {j : Fin n}
    (hj : IsFreeCol (rowReduce L) j) :
    ∃ v ∈ kerL L, v ≠ 0 ∧ hammingNorm v ≤ (rowReduce L).length + 1 := by sorry
