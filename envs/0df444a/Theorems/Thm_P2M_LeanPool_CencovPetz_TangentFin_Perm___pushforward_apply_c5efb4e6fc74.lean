-- Prove2me | Theorems.Thm_P2M_LeanPool_CencovPetz_TangentFin_Perm___pushforward_apply_c5efb4e6fc74
-- name    : P2M_LeanPool_CencovPetz_TangentFin_Perm___pushforward_apply_c5efb4e6fc74
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:34.388397+00:00
-- url     : https://prove2.me/theorems/6c349a72-d9ca-495b-853c-7dcbf08087c9
-- title:
--   P2 M Lean Pool Cencov Petz Tangent Fin Perm   pushforward apply c5efb4e6fc74: P2 M Lean Pool Cencov Petz Tangent Fin Perm   pushforward apply c5efb4e6fc74
-- statement:
--   The P2 M Lean Pool Cencov Petz Tangent Fin Perm   pushforward apply c5efb4e6fc74 construction uses the P2 M Lean Pool Cencov Petz Tangent Fin Perm   pushforward apply c5efb4e6fc74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L93-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L93-L98

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

theorem P2M_LeanPool_CencovPetz_TangentFin_Perm___pushforward_apply_c5efb4e6fc74 (σ : Equiv.Perm (Fin n)) (p : Simplex (Fin n)) (k : Fin n) :
    ((κ (n := n) σ).pushforward p).p k = p.p (σ.symm k) := by sorry

alias «LeanPool».«CencovPetz».«TangentFin».«Perm».«κ_pushforward_apply» := P2M_LeanPool_CencovPetz_TangentFin_Perm___pushforward_apply_c5efb4e6fc74
