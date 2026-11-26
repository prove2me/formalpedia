-- Prove2me | Theorems.Thm_Stanley_alternating_independent
-- name    : Stanley.alternating_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:18.321274+00:00
-- url     : https://prove2.me/theorems/0d29c455-1954-4f2a-96c4-63436d70f118
-- title:
--   Stanley: alternating independent
-- statement:
--   The Stanley construction uses the alternating independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/SourceSum.lean#L52-L57
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/SourceSum.lean#L52-L57

module
public import Definitions.Def_Stanley_Orientation
public import Definitions.Def_Stanley_SourceSum
set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
open Classical

theorem Stanley.alternating_independent [Nonempty V] :
    ∑ s : Finset V, (if Independent G (s : Set V) then
      (-1 : ℤ) ^ s.card * orientationCount (G.induce (s : Set V)ᶜ) else 0) = 0 := by sorry
