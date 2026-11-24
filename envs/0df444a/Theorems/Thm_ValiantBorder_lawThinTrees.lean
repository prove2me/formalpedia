-- Prove2me | Theorems.Thm_ValiantBorder_lawThinTrees
-- name    : ValiantBorder.lawThinTrees
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:16:00.124813+00:00
-- url     : https://prove2.me/theorems/4adcad18-3fc8-424f-b2d8-1778340eeaaa
-- title:
--   Building thin trees from exchange laws
-- statement:
--   A family of exchange laws on a unitriangular group satisfying the stated gain gives thin trees uniformly for all the allowed input sizes. The construction works after extending scalars to any commutative algebra over the coefficient ring.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Tree.lean#L1628).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Tree.lean#L1628.

import Definitions.Def_ValiantBorder_thinTrees

open Finset Nc Nc.Tow Nc.Vp Paper
open Nc.Tower (ee)

theorem ValiantBorder.lawThinTrees {A : Type} [CommRing A] {h : ℕ} [NeZero h]
    (VL : VLaws A (cNear (h := h)) (dNear (h := h)) 1 (2 ^ ee h)) (h3 : 3 ≤ h)
    (hgain : 1 + 8 * VL.C₁ ≤ (h : ℝ) / 4) :
    ∃ C : ℕ, ∀ (R : Type) [CommRing R] [Algebra A R] (M AA N ℓ : ℕ), 2 ≤ M → AA ≤ M → 1 ≤ N → 1 ≤ ℓ →
      Nonempty (ThinTrees R (((univ : Finset VL.Di).toList.map VL.L).map (lawMap (algebraMap A R))) AA N ℓ M
        (2 ^ ee h) (goodBound VL.C₁ VL.a₁) C (1 / Real.logb 2 ((2 ^ ee h : ℕ) : ℝ))) := by sorry
