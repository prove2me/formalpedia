-- Prove2me | Theorems.Thm_SumProduct_unit_separation
-- name    : SumProduct.unit_separation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:56:08.926339+00:00
-- url     : https://prove2.me/theorems/cfe27240-eac7-4290-aeeb-159241dcba49
-- title:
--   Sum Product: unit separation
-- statement:
--   **Lemma 3.6** (`lem-unitsep`, unit separation).
--
--   If `u` is a unit of `𝒪_K` such that `φ⁻¹ < |σ(u)| < φ` for every (real) infinite place `σ`
--   (`φ` the golden ratio), then `u = ±1`.
--
--   Elementary proof (suggested by GPT-5.5 Pro, replacing an appeal to Schinzel): the algebraic
--   integer `α = u² + u⁻² - 2 = (u - u⁻¹)²` has `0 ≤ σ(α) < 1` at every place, so `|N(α)| < 1`;
--   since `N(α) ∈ ℤ` this forces `α = 0`, i.e. `u = u⁻¹`, i.e. `u = ±1`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/UnitSeparation.lean#L29-L129
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/UnitSeparation.lean#L29-L129

import Mathlib
import Definitions.Def_SumProduct_UnitSeparation
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open Real NumberField NumberField.InfinitePlace

theorem SumProduct.unit_separation (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (u : (𝓞 K)ˣ)
    (h : ∀ w : InfinitePlace K,
      goldenRatio⁻¹ < w ((u : 𝓞 K) : K) ∧ w ((u : 𝓞 K) : K) < goldenRatio) :
    u = 1 ∨ u = -1 := by sorry
