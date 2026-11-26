-- Prove2me | Theorems.Thm_Stanley_alternating_sources
-- name    : Stanley.alternating_sources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:18.748795+00:00
-- url     : https://prove2.me/theorems/0f707c00-094e-4c11-823e-7780abd6c841
-- title:
--   Stanley: alternating sources
-- statement:
--   The Stanley construction uses the alternating sources property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/SourceSum.lean#L27-L49
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/SourceSum.lean#L27-L49

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

theorem Stanley.alternating_sources [Nonempty V] :
    ∑ s : Finset V, (-1 : ℤ) ^ s.card *
      (Fintype.card {D : AcyclicOrientation G // D.AllSources (s : Set V)} : ℤ) = 0 := by sorry
