-- Prove2me | Theorems.Thm_QECCertificates_finrank_spanL_le_length
-- name    : QECCertificates.finrank_spanL_le_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:15.109658+00:00
-- url     : https://prove2.me/theorems/cf15dfa1-2813-4f20-9709-a7a288cdaac5
-- title:
--   QECCertificates: finrank span L le length
-- statement:
--   **The dimension of `spanL A` is at most the length of `A`**: `A` is a generating
--   set.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L515-L528
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L515-L528

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.finrank_spanL_le_length (A : List (Vec n)) :
    Module.finrank (ZMod 2) (spanL A) ≤ A.length := by sorry
