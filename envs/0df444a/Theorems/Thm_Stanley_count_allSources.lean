-- Prove2me | Theorems.Thm_Stanley_count_allSources
-- name    : Stanley.count_allSources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:17.007812+00:00
-- url     : https://prove2.me/theorems/7e973018-8d8c-477b-999b-adb65987a64c
-- title:
--   Stanley: count all Sources
-- statement:
--   The Stanley construction uses the count all Sources property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/SourceSum.lean#L19-L24
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/SourceSum.lean#L19-L24

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

theorem Stanley.count_allSources (s : Finset V) :
    (Fintype.card {D : AcyclicOrientation G // D.AllSources (s : Set V)} : ℤ) =
      if Independent G (s : Set V) then orientationCount (G.induce (s : Set V)ᶜ) else 0 := by sorry
