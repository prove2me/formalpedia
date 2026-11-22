-- Prove2me | Theorems.Thm_QECCertificates_lp_trivialGroup_eq_hgp
-- name    : QECCertificates.lp_trivialGroup_eq_hgp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:11:11.553846+00:00
-- url     : https://prove2.me/theorems/bbff7dc7-69e7-40ca-99d0-ab3a2976bd90
-- title:
--   QECCertificates: lp trivial Group eq hgp
-- statement:
--   **On the trivial group ($\ell = 1$) LP is HGP entrywise** ($X$ side).
--
--   At $\ell = 1$ the group index has a single element (`Subsingleton G`), so $\delta_{\sigma\tau}$ is
--   constantly $1$ and the factor in `lpHX_liftConst_inl` disappears. This is the statement of the
--   literature that "for $R = \mathbb{F}_q$ the lifted product is equivalent to the product
--   construction" (Panteleev–Kalachev, p. 8).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L444-L449
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L444-L449

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.lp_trivialGroup_eq_hgp [Subsingleton G] [DecidableEq G] {mA nA mB nB : ℕ}
    (A : Matrix (Fin mA) (Fin nA) (ZMod 2)) (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (i : Fin mA) (s : Fin mB) (j : Fin nA) (t : Fin mB) (σ τ : G) :
    lpHX (liftConst A) (liftConst B) ((i, s), σ) (Sum.inl ((j, t), τ))
      = hgpHX A B.transpose (i, s) (Sum.inl (j, t)) := by sorry
