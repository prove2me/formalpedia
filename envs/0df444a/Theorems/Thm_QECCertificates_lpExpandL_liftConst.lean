-- Prove2me | Theorems.Thm_QECCertificates_lpExpandL_liftConst
-- name    : QECCertificates.lpExpandL_liftConst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:34.156148+00:00
-- url     : https://prove2.me/theorems/7ba34ebe-34e4-45d8-9280-e28c740bbb25
-- title:
--   QECCertificates: lp Expand L lift Const
-- statement:
--   With a constant seed the left regular block expansion degenerates to $B \otimes I_\ell$.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L388-L394
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L388-L394

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.lpExpandL_liftConst [DecidableEq G] {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (s : Fin m) (σ : G) (t : Fin n) (τ : G) :
    lpExpandL (liftConst B) (s, σ) (t, τ) = B s t * (if σ = τ then 1 else 0) := by sorry
