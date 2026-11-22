-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_annulusContribution_eq_of_mem
-- name    : PebblingLean.Hypercube.annulusContribution_eq_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:51:29.532539+00:00
-- url     : https://prove2.me/theorems/f6b9288f-f953-4dae-8d2e-e044641c5f2d
-- title:
--   Hypercube: annulus Contribution eq of mem
-- statement:
--   The Hypercube construction uses the annulus Contribution eq of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBound.lean#L48-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBound.lean#L48-L52

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling

theorem PebblingLean.Hypercube.annulusContribution_eq_of_mem {n rIn rOut : ℕ}
    {target center : HypercubeVertex n}
    (hmem : center ∈ annulus n rIn rOut target) :
    annulusContribution rIn rOut target center = 2 ^ (rOut - dist center target) := by sorry
