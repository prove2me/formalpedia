-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_dist_eq_zero_iff
-- name    : PebblingLean.Hypercube.dist_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:06.957447+00:00
-- url     : https://prove2.me/theorems/0c0b4ad7-490b-41a8-8cbc-39340cfdebf3
-- title:
--   Hypercube: dist eq zero iff
-- statement:
--   The Hypercube construction uses the dist eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Hypercube.lean#L114-L124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Hypercube.lean#L114-L124

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube

theorem PebblingLean.Hypercube.dist_eq_zero_iff {n : ℕ} {x y : HypercubeVertex n} :
    dist x y = 0 ↔ x = y := by sorry
