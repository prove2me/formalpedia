-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_bernsteinExponent_two_width_mul_T_ge
-- name    : PebblingLean.Hypercube.bernsteinExponent_two_width_mul_T_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:53:53.74993+00:00
-- url     : https://prove2.me/theorems/cbca77c6-ca20-416f-b5b1-a0c7adb4fea8
-- title:
--   Hypercube: bernstein Exponent two width mul T ge
-- statement:
--   The constant calculation used in the paper after Bernstein is applied with
--   variance proxy `2 * B * T`, scale `B`, and gap `delta*T/4`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1731-L1761
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1731-L1761

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability

theorem PebblingLean.Hypercube.bernsteinExponent_two_width_mul_T_ge
    {delta T B : ℝ} (hdelta_nonneg : 0 ≤ delta) (hdelta_le : delta ≤ 1 / 2)
    (hT_pos : 0 < T) (hB_pos : 0 < B) :
    (delta ^ 2 * T) / (96 * B) ≤
      bernsteinExponent (2 * B * T) B (delta * T / 4) := by sorry
