-- Prove2me | Theorems.Thm_P2M_LeanPool_CencovPetz_TangentFin_Perm___pushforward_uniform_cb98e5b2dde2
-- name    : P2M_LeanPool_CencovPetz_TangentFin_Perm___pushforward_uniform_cb98e5b2dde2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:34.774773+00:00
-- url     : https://prove2.me/theorems/2b84f311-3350-477d-bad9-9795b316331f
-- title:
--   P2 M Lean Pool Cencov Petz Tangent Fin Perm   pushforward uniform cb98e5b2dde2: P2 M Lean Pool Cencov Petz Tangent Fin Perm   pushforward uniform cb98e5b2dde2
-- statement:
--   The P2 M Lean Pool Cencov Petz Tangent Fin Perm   pushforward uniform cb98e5b2dde2 construction uses the P2 M Lean Pool Cencov Petz Tangent Fin Perm   pushforward uniform cb98e5b2dde2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L114-L119
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L114-L119

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

theorem P2M_LeanPool_CencovPetz_TangentFin_Perm___pushforward_uniform_cb98e5b2dde2 {n : ℕ} [Nonempty (Fin n)] (σ : Equiv.Perm (Fin n)) :
    (κ (n := n) σ).pushforward (Simplex.uniform (α := Fin n)) = Simplex.uniform (α := Fin n) := by sorry

alias «LeanPool».«CencovPetz».«TangentFin».«Perm».«κ_pushforward_uniform» := P2M_LeanPool_CencovPetz_TangentFin_Perm___pushforward_uniform_cb98e5b2dde2
