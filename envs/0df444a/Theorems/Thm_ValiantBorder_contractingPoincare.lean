-- Prove2me | Theorems.Thm_ValiantBorder_contractingPoincare
-- name    : ValiantBorder.contractingPoincare
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:10:15.94434+00:00
-- url     : https://prove2.me/theorems/5fb0946a-dc76-4baa-b200-804456180d78
-- title:
--   A Poincaré inequality on unitriangular groups over a contracting field
-- statement:
--   For a contracting field there are an integer $u≥2$ and a constant $C≥0$ such that, in every unitriangular group of height $lu$ with $l≥2$, the mean squared price of a pair is at most $C$ times the sum of the mean squared prices of the simple-transvection edges.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Groups.lean#L1085-L1113).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Groups.lean#L1085-L1113.

import Definitions.Def_ValiantBorder_cutLaws

open Finset Nc.Tower

theorem ValiantBorder.contractingPoincare {K : Type} [Field K] (hK : Paper.Contracting K) :
    ∃ u : ℕ, 2 ≤ u ∧ ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ l : ℕ, 2 ≤ l → ∀ w : U (l * u) → U (l * u) → ℝ, Nc.Price.IsPrice K w →
      (∑ g, ∑ k, w k (g * k) ^ 2) / (Fintype.card (U (l * u)) : ℝ) ^ 2 ≤
        C₀ * ∑ j, (∑ k, w k (x (l * u) j * k) ^ 2) / (Fintype.card (U (l * u)) : ℝ) := by sorry
