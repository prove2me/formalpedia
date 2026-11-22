-- Prove2me | Theorems.Thm_QECCertificates_lp_trivialGroup_eq_hgp_Z
-- name    : QECCertificates.lp_trivialGroup_eq_hgp_Z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:11:08.069801+00:00
-- url     : https://prove2.me/theorems/fc4bfaeb-fbc2-49b2-933f-dcd4d34bb6b6
-- title:
--   QECCertificates: lp trivial Group eq hgp Z
-- statement:
--   **On the trivial group ($\ell = 1$) LP is HGP entrywise** ($Z$ side).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L452-L457
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L452-L457

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.lp_trivialGroup_eq_hgp_Z [Subsingleton G] [DecidableEq G] {mA nA mB nB : ℕ}
    (A : Matrix (Fin mA) (Fin nA) (ZMod 2)) (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (j : Fin nA) (t : Fin nB) (j' : Fin nA) (s : Fin mB) (σ τ : G) :
    lpHZ (liftConst A) (liftConst B) ((j, t), σ) (Sum.inl ((j', s), τ))
      = hgpHZ A B.transpose (j, t) (Sum.inl (j', s)) := by sorry
