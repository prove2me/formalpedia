-- Prove2me | Theorems.Thm_QECCertificates_lp_row_count_X
-- name    : QECCertificates.lp_row_count_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:50.683064+00:00
-- url     : https://prove2.me/theorems/1baf8662-46f3-44a6-9cdb-1a1c3ee13c7e
-- title:
--   QECCertificates: lp row count X
-- statement:
--   The number of X-type check rows of LP: $m_A m_B \ell$.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L352-L354
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L352-L354

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

theorem QECCertificates.lp_row_count_X [Fintype G] {mA mB : ℕ} :
    Fintype.card ((Fin mA × Fin mB) × G) = mA * mB * Fintype.card G := by sorry
