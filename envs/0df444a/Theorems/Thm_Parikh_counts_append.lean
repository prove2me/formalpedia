-- Prove2me | Theorems.Thm_Parikh_counts_append
-- name    : Parikh.counts_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:47:46.178803+00:00
-- url     : https://prove2.me/theorems/1c6ce0ef-b12a-4b93-8732-2a20da892330
-- title:
--   Parikh: counts append
-- statement:
--   Concatenation adds count vectors (`eq:word-add`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Counting.lean#L74-L77
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Counting.lean#L74-L77

module
public import Mathlib.Computability.Language
public import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Definitions.Def_LeanPool_Parikh_Counting
set_option autoImplicit true
@[expose] public section
public section
open scoped Pointwise
open Parikh

theorem Parikh.counts_append {T : Type*} [DecidableEq T] (u v : List T) :
    counts (u ++ v) = counts u + counts v := by sorry
