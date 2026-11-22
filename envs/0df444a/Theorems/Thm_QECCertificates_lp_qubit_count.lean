-- Prove2me | Theorems.Thm_QECCertificates_lp_qubit_count
-- name    : QECCertificates.lp_qubit_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:49.077977+00:00
-- url     : https://prove2.me/theorems/3f4c0c0a-1fd2-4555-a03e-216e782a11ca
-- title:
--   QECCertificates: lp qubit count
-- statement:
--   **The number of qubits of LP**: $\ell\,(n_A m_B + m_A n_B)$.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L343-L348
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L343-L348

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

theorem QECCertificates.lp_qubit_count [Fintype G] {mA nA mB nB : ℕ} :
    Fintype.card (((Fin nA × Fin mB) × G) ⊕ ((Fin mA × Fin nB) × G))
      = (nA * mB + mA * nB) * Fintype.card G := by sorry
