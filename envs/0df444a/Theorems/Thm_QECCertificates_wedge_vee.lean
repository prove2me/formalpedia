-- Prove2me | Theorems.Thm_QECCertificates_wedge_vee
-- name    : QECCertificates.wedge_vee
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:08.86792+00:00
-- url     : https://prove2.me/theorems/e1c8a686-f3b4-4795-8718-7e2c045b5f40
-- title:
--   QECCertificates: wedge vee
-- statement:
--   `wedge` after `vee` is the identity (everywhere): `vee` is a right inverse of
--   `wedge`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L227-L236
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L227-L236

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

theorem QECCertificates.wedge_vee {u : Fin a → Vec p} {L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)}
    (hleft : ∀ c : Fin a → ZMod 2, L (∑ k, c k • u k) = c) (C : VMat a s) :
    wedge L (vee u C) = C := by sorry
