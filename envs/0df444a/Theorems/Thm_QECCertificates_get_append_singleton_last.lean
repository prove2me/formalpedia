-- Prove2me | Theorems.Thm_QECCertificates_get_append_singleton_last
-- name    : QECCertificates.get_append_singleton_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:11:48.481461+00:00
-- url     : https://prove2.me/theorems/e3dc1ab7-6172-4311-8e7f-f611b5e414c7
-- title:
--   QECCertificates: get append singleton last
-- statement:
--   The last element of `(D ++ [x])` is `x`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L268-L271
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L268-L271

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.get_append_singleton_last (D : List (PivRow n)) (x : PivRow n) :
    (D ++ [x]).get ⟨D.length, by have h := length_append_singleton D x; omega⟩ = x := by sorry
