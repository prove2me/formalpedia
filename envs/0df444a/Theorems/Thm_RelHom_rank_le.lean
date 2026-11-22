-- Prove2me | Theorems.Thm_RelHom_rank_le
-- name    : RelHom.rank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:27.9902+00:00
-- url     : https://prove2.me/theorems/9a228f6a-c900-4968-a4c6-1b90ad9f274b
-- title:
--   Rel Hom: rank le
-- statement:
--   **A relation homomorphism does not increase rank.** If `f : r →r s` maps `r` into a
--   well-founded relation `s`, then the `r`-rank of `a` is at most the `s`-rank of `f a`. This is the
--   cross-relation companion to `IsWellFounded.rank_lt_of_rel` (which only compares ranks within a
--   single relation), and the tool underlying the rank comparisons for the ray and the restriction of
--   a front. General; Mathlib-bound (belongs next to `IsWellFounded.rank_lt_of_rel`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Rank.lean#L50-L65
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Rank.lean#L50-L65

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Defs
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
set_option autoImplicit true
@[expose] public section
public section
open Set List Ordinal
universe u
noncomputable section

theorem RelHom.rank_le {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellFounded α r] [IsWellFounded β s] (f : r →r s) (a : α) :
    IsWellFounded.rank r a ≤ IsWellFounded.rank s (f a) := by sorry
