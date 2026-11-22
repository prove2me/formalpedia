-- Prove2me | Theorems.Thm_P2M_LeanPool_CencovPetz_eq_of_eqOn_dense__9bd0a7151849
-- name    : P2M_LeanPool_CencovPetz_eq_of_eqOn_dense__9bd0a7151849
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:16.861425+00:00
-- url     : https://prove2.me/theorems/96dd8535-8931-4444-980e-d48a9582dce4
-- title:
--   P2 M Lean Pool Cencov Petz eq of eq On dense  9bd0a7151849: P2 M Lean Pool Cencov Petz eq of eq On dense  9bd0a7151849
-- statement:
--   The P2 M Lean Pool Cencov Petz eq of eq On dense  9bd0a7151849 construction uses the P2 M Lean Pool Cencov Petz eq of eq On dense  9bd0a7151849 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/ContinuousExtension.lean#L39-L53
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/ContinuousExtension.lean#L39-L53

module
public import Definitions.Def_LeanPool_CencovPetz_SimplexTopology
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Topology.Metrizable.Uniformity
public import Definitions.Def_LeanPool_CencovPetz_ContinuousExtension
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {α : Type u} [Fintype α]

theorem P2M_LeanPool_CencovPetz_eq_of_eqOn_dense__9bd0a7151849 {s : Set (Simplex α)} (hs : Dense s)
    {f g : Simplex α → tangentSpace (α := α) → tangentSpace (α := α) → ℝ}
    (hf : ∀ u v, Continuous fun p : Simplex α => f p u v)
    (hg : ∀ u v, Continuous fun p : Simplex α => g p u v)
    (hfg : ∀ p ∈ s, ∀ u v, f p u v = g p u v) :
    ∀ p u v, f p u v = g p u v := by sorry

alias «LeanPool».«CencovPetz».«eq_of_eqOn_dense₂» := P2M_LeanPool_CencovPetz_eq_of_eqOn_dense__9bd0a7151849
