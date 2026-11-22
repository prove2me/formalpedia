-- Prove2me | Theorems.Thm_QECCertificates_lp_row_count_Z
-- name    : QECCertificates.lp_row_count_Z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:52.079316+00:00
-- url     : https://prove2.me/theorems/a770f680-0804-46e9-be7b-9e9ee638dbee
-- title:
--   QECCertificates: lp row count Z
-- statement:
--   The number of Z-type check rows of LP: $n_A n_B \ell$.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L358-L360
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L358-L360

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]
omit [Group G]

theorem QECCertificates.lp_row_count_Z [Fintype G] {nA nB : ℕ} :
    Fintype.card ((Fin nA × Fin nB) × G) = nA * nB * Fintype.card G := by sorry
