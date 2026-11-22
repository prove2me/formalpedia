-- Prove2me | Theorems.Thm_QECCertificates_mem_spanL_append_singleton_of_add_mem
-- name    : QECCertificates.mem_spanL_append_singleton_of_add_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:36.766001+00:00
-- url     : https://prove2.me/theorems/610761c5-36c1-4f07-be64-1edde611f789
-- title:
--   QECCertificates: mem span L append singleton of add mem
-- statement:
--   If `v + w` lies in the row space of `A`, then appending `w` and appending `v` span
--   the same row space. (The row produced by elimination differs from the original one by a
--   vector that is already in the row space, so the row space is unchanged.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L156-L161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L156-L161

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.mem_spanL_append_singleton_of_add_mem {A : List (Vec n)} {v w : Vec n}
    (h : v + w ∈ spanL A) : w ∈ spanL (A ++ [v]) := by sorry
