-- Prove2me | Theorems.Thm_QECCertificates_finrank_spanL_append_le_of_mem
-- name    : QECCertificates.finrank_spanL_append_le_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:15.919509+00:00
-- url     : https://prove2.me/theorems/33f96fb0-0534-4e19-ae63-d4c9fa0a69e2
-- title:
--   QECCertificates: finrank span L append le of mem
-- statement:
--   **A rank upper bound from redundant generators (prefix form)**: write the list of
--   rows as `A ++ B`; if every row of `B` lies in `spanL A`, then the dimension of the whole
--   list is at most `A.length`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L544-L553
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L544-L553

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.finrank_spanL_append_le_of_mem (A B : List (Vec n))
    (h : ∀ v ∈ B, v ∈ spanL A) :
    Module.finrank (ZMod 2) (spanL (A ++ B)) ≤ A.length := by sorry
