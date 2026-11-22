-- Prove2me | Theorems.Thm_P2M_GridHam_getLast__eq_getLast_of_ne_nil_6bb10de92c8a
-- name    : P2M_GridHam_getLast__eq_getLast_of_ne_nil_6bb10de92c8a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:23:58.399591+00:00
-- url     : https://prove2.me/theorems/4ececd6e-728b-4f16-b60b-8eb64c6a2f7d
-- title:
--   P2 M Grid Ham get Last  eq get Last of ne nil 6bb10de92c8a: P2 M Grid Ham get Last  eq get Last of ne nil 6bb10de92c8a
-- statement:
--   Bridges `List.getLast?` (which returns `Option`) to `List.getLast`
--   (which takes a nonempty-proof and returns the element directly): if the
--   former says `some x`, the latter computes to `x`. Proved from scratch by
--   induction rather than by citing a Mathlib lemma name -- see the note above
--   `chain_parity_head_last` for why. Each step relies only on `rfl` (both
--   `List.getLast` and `List.getLast?` reduce definitionally on a concrete
--   `cons`/`cons`/... pattern, exactly like `chainAdjacent` did in
--   `chain_parity_alternates` above) plus `injection` (a core tactic, not a
--   named lemma) to extract `a = x` from `some a = some x`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L85-L103
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L85-L103

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem P2M_GridHam_getLast__eq_getLast_of_ne_nil_6bb10de92c8a :
    ∀ (l : List Coord) (hne : l ≠ []) (x : Coord),
      l.getLast? = some x → l.getLast hne = x := by sorry

alias «GridHam».«getLast?_eq_getLast_of_ne_nil» := P2M_GridHam_getLast__eq_getLast_of_ne_nil_6bb10de92c8a
