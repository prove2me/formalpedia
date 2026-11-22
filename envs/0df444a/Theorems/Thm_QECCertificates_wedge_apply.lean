-- Prove2me | Theorems.Thm_QECCertificates_wedge_apply
-- name    : QECCertificates.wedge_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:44:03.529802+00:00
-- url     : https://prove2.me/theorems/39e697f3-6481-40a3-b09d-37049481b3ad
-- title:
--   QECCertificates: wedge apply
-- statement:
--   The QECCertificates construction uses the wedge apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L211-L212
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean#L211-L212

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

theorem QECCertificates.wedge_apply (L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)) (X : VMat p s)
    (k : Fin a) (j : Fin s) : wedge L X (k, j) = L (colOf X j) k := by sorry

attribute [defeq] QECCertificates.wedge_apply
