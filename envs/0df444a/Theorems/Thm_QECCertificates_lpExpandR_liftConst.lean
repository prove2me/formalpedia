-- Prove2me | Theorems.Thm_QECCertificates_lpExpandR_liftConst
-- name    : QECCertificates.lpExpandR_liftConst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:30.021714+00:00
-- url     : https://prove2.me/theorems/bf311224-f180-44d4-8279-4e084ff83e42
-- title:
--   QECCertificates: lp Expand R lift Const
-- statement:
--   With a constant seed the right regular block expansion degenerates to $A \otimes I_\ell$:
--   $\widehat A\,(i,\sigma)(j,\tau) = A_{ij}\cdot[\sigma = \tau]$.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L379-L385
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L379-L385

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.lpExpandR_liftConst [DecidableEq G] {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (i : Fin m) (σ : G) (j : Fin n) (τ : G) :
    lpExpandR (liftConst A) (i, σ) (j, τ) = A i j * (if σ = τ then 1 else 0) := by sorry
