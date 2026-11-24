-- Prove2me | Theorems.Thm_ValiantBorder_contractingLaws
-- name    : ValiantBorder.contractingLaws
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:03:52.294965+00:00
-- url     : https://prove2.me/theorems/23f7c3ba-238d-4260-ac1a-2d84622b05a4
-- title:
--   Contracting fields admit exchange laws with quantitative gain
-- statement:
--   Over a finitely generated integer subring of every contracting field, exchange laws exist on the chambers of a unitriangular group of some height $h≥3$. Their contraction constant satisfies $1+8C_1≤h/4$, and $2C_1a_1^2$ is a natural number.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Laws.lean#L456).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Laws.lean#L456.

import Definitions.Def_ValiantBorder_cutLaws

theorem ValiantBorder.contractingLaws {K : Type} [Field K] (hK : Paper.Contracting K) :
    ∃ (h : ℕ) (_ : NeZero h), 3 ≤ h ∧ ∃ (A : Subring K) (_ : Algebra.FiniteType ℤ A)
      (VL : Nc.Tow.VLaws A (Nc.Vp.cNear (h := h)) (Nc.Vp.dNear (h := h)) 1 (2 ^ Nc.Tower.ee h)),
        1 + 8 * VL.C₁ ≤ (h : ℝ) / 4 ∧ ∃ g : ℕ, 2 * VL.C₁ * (VL.a₁ : ℝ) ^ 2 = g := by sorry
