-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_toward_injective
-- name    : ParallelPostulate.HyperbolicPlane.toward_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:06:16.687944+00:00
-- url     : https://prove2.me/theorems/5a271636-d731-4369-a86b-c0294f898908
-- title:
--   Hyperbolic Plane: toward injective
-- statement:
--   Lines from `P` toward different numbers of `L` are different lines of the plane.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L681-L706
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L681-L706

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
variable {K : Type*} [Field K]

theorem ParallelPostulate.HyperbolicPlane.toward_injective (Pl : Set (K × K)) (hopen : OpenAlong Pl) (L : Dim K)
    (hL : L.zero ≠ L.one) {P : K × K} (hP : P ∈ Pl) (hPL : P ∉ L.points) :
    Function.Injective (toward Pl L P) := by sorry
