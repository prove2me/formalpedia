-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_annulusContribution_eq_zero_of_notMem
-- name    : PebblingLean.Hypercube.annulusContribution_eq_zero_of_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:51:26.144983+00:00
-- url     : https://prove2.me/theorems/9c8fd833-57bc-4077-856a-d22d124960e5
-- title:
--   Hypercube: annulus Contribution eq zero of not Mem
-- statement:
--   The Hypercube construction uses the annulus Contribution eq zero of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBound.lean#L54-L60
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBound.lean#L54-L60

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

theorem PebblingLean.Hypercube.annulusContribution_eq_zero_of_notMem {n rIn rOut : ℕ}
    {target center : HypercubeVertex n}
    (hmem : center ∉ annulus n rIn rOut target) :
    annulusContribution rIn rOut target center = 0 := by sorry
