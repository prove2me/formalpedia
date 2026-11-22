-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_one_le_weight_of_solvable
-- name    : PebblingLean.Hypercube.one_le_weight_of_solvable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:50:45.516241+00:00
-- url     : https://prove2.me/theorems/cc4139ad-42b9-4bee-8666-32d01e46c7db
-- title:
--   Hypercube: one le weight of solvable
-- statement:
--   A solvable distribution has target weight at least one for every target.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/LowerBound.lean#L50-L53
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/LowerBound.lean#L50-L53

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Definitions.Def_LeanPool_PebblingLean_Weight
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling

theorem PebblingLean.Hypercube.one_le_weight_of_solvable {n : ℕ} {D : Pebbling (HypercubeVertex n)}
    (hsolv : Solvable (graph n) D) (target : HypercubeVertex n) :
    1 ≤ weight dist D target := by sorry
