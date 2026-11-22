-- Prove2me | Theorems.Thm_QECCertificates_hammingNorm_kerVec_le
-- name    : QECCertificates.hammingNorm_kerVec_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:40.138219+00:00
-- url     : https://prove2.me/theorems/3311557a-4271-4469-8d97-f5e930e1b3bd
-- title:
--   QECCertificates: hamming Norm ker Vec le
-- statement:
--   **The Singleton-type count**: the support of a kernel vector lies in
--   $\{j\}\cup$ the pivot columns, so its weight is at most $1+\#D$.
--
--   This holds for **every** column `j`, free or not: `kerVec D j` can be nonzero only at `j`
--   and at the pivot columns, and every other column is free and hence vanishes by
--   `kerVec_apply_free`. There are exactly `#D` pivot columns, and `#D` is the rank. Together
--   with `kerVec_ne_zero` this makes "a nontrivial kernel $\Rightarrow$ there is a nonzero
--   kernel vector of weight $\le\rho+1$" a theorem rather than an informal remark.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L239-L257
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L239-L257

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.hammingNorm_kerVec_le (D : List (PivRow n)) (j : Fin n) :
    hammingNorm (kerVec D j) ≤ D.length + 1 := by sorry
