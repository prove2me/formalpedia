-- Prove2me | Theorems.Thm_SumProduct_lattice_count_add
-- name    : SumProduct.lattice_count_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:52:17.694862+00:00
-- url     : https://prove2.me/theorems/7732ebf0-e17a-41da-a81d-55ac06655286
-- title:
--   Sum Product: lattice count add
-- statement:
--   **Lemma 3.5** (`lem-ball`, additive lattice-point count).
--
--   For a totally real field of degree `d` and `X ≥ 0`,
--   `X^d / √Δ_K ≤ |B⁺(X)| ≤ (2X+1)^d`. The lower bound is Blichfeldt's lemma applied to the
--   Minkowski lattice (covolume `√Δ_K`); the upper bound is an `L^∞` packing argument using that
--   distinct algebraic integers are `1`-separated in some embedding (`|N(x−y)| ≥ 1`).
--
--   (For `0 ≤ X < 1` the lower bound is trivial: `X^d/√Δ_K ≤ 1 ≤ |B⁺(X)|` as `0 ∈ B⁺(X)`.)
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L454-L458
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/AdditiveCount.lean#L454-L458

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct

theorem SumProduct.lattice_count_add (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (d : ℕ) (hd : Module.finrank ℚ K = d) (X : ℝ) (hX : 0 ≤ X) :
    X ^ d / Real.sqrt |(NumberField.discr K : ℝ)| ≤ (boxAdd K X).card ∧
      ((boxAdd K X).card : ℝ) ≤ (2 * X + 1) ^ d := by sorry
