-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_diffSet_fromDiffSet_insert
-- name    : PebblingLean.Hypercube.diffSet_fromDiffSet_insert
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:51:20.336786+00:00
-- url     : https://prove2.me/theorems/28ed582d-399e-42fa-85b4-f19203fe009d
-- title:
--   Hypercube: diff Set from Diff Set insert
-- statement:
--   The Hypercube construction uses the diff Set from Diff Set insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubePath.lean#L38-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubePath.lean#L38-L49

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Definitions.Def_LeanPool_PebblingLean_Delivery
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_PebblingLean_HypercubePath
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling

theorem PebblingLean.Hypercube.diffSet_fromDiffSet_insert {n : ℕ} (base : HypercubeVertex n)
    {s : Finset (Fin n)} {i : Fin n} (hi : i ∉ s) :
    diffSet (fromDiffSet base s) (fromDiffSet base (insert i s)) = {i} := by sorry
