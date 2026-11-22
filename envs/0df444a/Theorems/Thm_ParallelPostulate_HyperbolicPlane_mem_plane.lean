-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_mem_plane
-- name    : ParallelPostulate.HyperbolicPlane.mem_plane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:04:21.849288+00:00
-- url     : https://prove2.me/theorems/11cba04e-03f9-4ec3-b147-70297c6ab7e6
-- title:
--   Hyperbolic Plane: mem plane
-- statement:
--   The Hyperbolic Plane construction uses the mem plane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L851-L852
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L851-L852

module
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
omit [IsStrictOrderedRing K]

theorem ParallelPostulate.HyperbolicPlane.mem_plane {κ : K} {p : K × K} : p ∈ plane κ ↔ 0 < 1 + κ * (p.1 ^ 2 + p.2 ^ 2) := by sorry
