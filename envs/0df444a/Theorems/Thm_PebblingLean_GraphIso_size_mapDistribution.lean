-- Prove2me | Theorems.Thm_PebblingLean_GraphIso_size_mapDistribution
-- name    : PebblingLean.GraphIso.size_mapDistribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:49:59.702824+00:00
-- url     : https://prove2.me/theorems/12b0ffda-03ef-4c68-918c-ec90ad8f1c2c
-- title:
--   Graph Iso: size map Distribution
-- statement:
--   The Graph Iso construction uses the size map Distribution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/GraphIso.lean#L45-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/GraphIso.lean#L45-L49

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_GraphIso
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.GraphIso
variable {V : Type u} {W : Type v} {G : Graph V} {H : Graph W}

theorem PebblingLean.GraphIso.size_mapDistribution [Fintype V] [Fintype W]
    (iso : GraphIso G H) (D : Pebbling V) :
    Pebbling.size (iso.mapDistribution D) = Pebbling.size D := by sorry
