-- Prove2me | Theorems.Thm_QECCertificates_lp2_orthogonal
-- name    : QECCertificates.lp2_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:42.9478+00:00
-- url     : https://prove2.me/theorems/d1dac0cd-075b-4488-8b29-90db668be850
-- title:
--   QECCertificates: lp2 orthogonal
-- statement:
--   **CSS compatibility of 2BGA**: $H_X H_Z^{\top} = L(a)R(b) + R(b)L(a) = 0$.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L331-L337
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LiftedProduct.lean#L331-L337

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]

theorem QECCertificates.lp2_orthogonal [Fintype G] (a b : G → ZMod 2) :
    lp2HX a b * (lp2HZ a b).transpose = 0 := by sorry
