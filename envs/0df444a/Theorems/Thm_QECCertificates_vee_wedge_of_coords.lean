-- Prove2me | Theorems.Thm_QECCertificates_vee_wedge_of_coords
-- name    : QECCertificates.vee_wedge_of_coords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:14.793219+00:00
-- url     : https://prove2.me/theorems/075436bf-7100-44c8-bac2-aacf4ce86fb1
-- title:
--   QECCertificates: vee wedge of coords
-- statement:
--   `vee` after `wedge` is the identity (on the column-constrained space): `vee` is a left
--   inverse of `wedge`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L216-L223
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L216-L223

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {p q r s a b : ℕ}

theorem QECCertificates.vee_wedge_of_coords {u : Fin a → Vec p} {L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)}
    {U : Submodule (ZMod 2) (Vec p)}
    (hcoords : ∀ x ∈ U, ∑ k, L x k • u k = x) {X : VMat p s} (hX : ∀ j, colOf X j ∈ U) :
    vee u (wedge L X) = X := by sorry
