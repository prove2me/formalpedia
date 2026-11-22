-- Prove2me | Theorems.Thm_QECCertificates_snocV_zero_zero
-- name    : QECCertificates.snocV_zero_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:42:52.551704+00:00
-- url     : https://prove2.me/theorems/b8a77c97-0e8d-4c1c-9f05-1bd6da1b577f
-- title:
--   QECCertificates: snoc V zero zero
-- statement:
--   A zero vector padded with a zero at the last position is still the zero vector.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L87-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/WeightEnum.lean#L87-L91

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.snocV_zero_zero : snocV (0 : Vec n) (0 : ZMod 2) = 0 := by sorry
