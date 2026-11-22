-- Prove2me | Theorems.Thm_P2M_LeanPool_CencovPetz_TangentFin_Perm___tangentPushforward_dij_a3e9a546b358
-- name    : P2M_LeanPool_CencovPetz_TangentFin_Perm___tangentPushforward_dij_a3e9a546b358
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:34.104669+00:00
-- url     : https://prove2.me/theorems/3b2a430c-2b2c-491c-9d88-1961d6c198f6
-- title:
--   P2 M Lean Pool Cencov Petz Tangent Fin Perm   tangent Pushforward dij a3e9a546b358: P2 M Lean Pool Cencov Petz Tangent Fin Perm   tangent Pushforward dij a3e9a546b358
-- statement:
--   The P2 M Lean Pool Cencov Petz Tangent Fin Perm   tangent Pushforward dij a3e9a546b358 construction uses the P2 M Lean Pool Cencov Petz Tangent Fin Perm   tangent Pushforward dij a3e9a546b358 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L121-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L121-L127

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

theorem P2M_LeanPool_CencovPetz_TangentFin_Perm___tangentPushforward_dij_a3e9a546b358 (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (κ (n := n) σ).tangentPushforward (Basis.dij (n := n) i j) =
      Basis.dij (n := n) (σ i) (σ j) := by sorry

alias «LeanPool».«CencovPetz».«TangentFin».«Perm».«κ_tangentPushforward_dij» := P2M_LeanPool_CencovPetz_TangentFin_Perm___tangentPushforward_dij_a3e9a546b358
