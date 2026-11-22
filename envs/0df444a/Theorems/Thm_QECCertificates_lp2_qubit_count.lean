-- Prove2me | Theorems.Thm_QECCertificates_lp2_qubit_count
-- name    : QECCertificates.lp2_qubit_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:53.675809+00:00
-- url     : https://prove2.me/theorems/4dace20b-c8aa-4c8e-8940-81e0ff9f792c
-- title:
--   QECCertificates: lp2 qubit count
-- statement:
--   **The code length of 2BGA**: $n = 2\ell$ (the direct sum of two $\ell$ blocks).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L364-L366
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L364-L366

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

theorem QECCertificates.lp2_qubit_count [Fintype G] : Fintype.card (G ⊕ G) = 2 * Fintype.card G := by sorry
