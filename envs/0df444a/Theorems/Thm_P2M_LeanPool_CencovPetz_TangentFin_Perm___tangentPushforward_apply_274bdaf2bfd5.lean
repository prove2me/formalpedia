-- Prove2me | Theorems.Thm_P2M_LeanPool_CencovPetz_TangentFin_Perm___tangentPushforward_apply_274bdaf2bfd5
-- name    : P2M_LeanPool_CencovPetz_TangentFin_Perm___tangentPushforward_apply_274bdaf2bfd5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:31.308801+00:00
-- url     : https://prove2.me/theorems/6ee42304-d7e5-471b-902a-e994cf96e8ff
-- title:
--   P2 M Lean Pool Cencov Petz Tangent Fin Perm   tangent Pushforward apply 274bdaf2bfd5: P2 M Lean Pool Cencov Petz Tangent Fin Perm   tangent Pushforward apply 274bdaf2bfd5
-- statement:
--   The P2 M Lean Pool Cencov Petz Tangent Fin Perm   tangent Pushforward apply 274bdaf2bfd5 construction uses the P2 M Lean Pool Cencov Petz Tangent Fin Perm   tangent Pushforward apply 274bdaf2bfd5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L86-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L86-L91

module
public import Definitions.Def_LeanPool_CencovPetz_UniformSimplex
public import Definitions.Def_LeanPool_CencovPetz_MonotoneMetric
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariance
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariantBilinForm
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {n : ℕ}
open LeanPool.CencovPetz.TangentFin
open LeanPool.CencovPetz.TangentFin.Perm
open _root_.LeanPool.CencovPetz.TangentFin.Basis

theorem P2M_LeanPool_CencovPetz_TangentFin_Perm___tangentPushforward_apply_274bdaf2bfd5 (σ : Equiv.Perm (Fin n)) (u : V n) (k : Fin n) :
    ((κ (n := n) σ).tangentPushforward u : Fin n → ℝ) k = (u : Fin n → ℝ) (σ.symm k) := by sorry

alias «LeanPool».«CencovPetz».«TangentFin».«Perm».«κ_tangentPushforward_apply» := P2M_LeanPool_CencovPetz_TangentFin_Perm___tangentPushforward_apply_274bdaf2bfd5
