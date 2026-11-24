-- Prove2me | Theorems.Thm_ValiantBorder_contractingApproxRate
-- name    : ValiantBorder.contractingApproxRate
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:23:35.851362+00:00
-- url     : https://prove2.me/theorems/f1fa5a35-74db-4290-aa20-7198d380674f
-- title:
--   Circuit lower bound in the contracting case
-- statement:
--   Fix a contracting field and a grid-complete family. There is a constant $c>0$ such that for all sufficiently large $m$, each Laurent-series approximating circuit has more than $2^{c(\log_2 m)^2/\log_2(\log_2 m)}$ gates.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Approximate.lean#L241-L248).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Approximate.lean#L241-L248.

import Definitions.Def_ValiantBorder_fieldCases
import Definitions.Def_ValiantBorder_gridComplete
import Definitions.Def_VP_VNP_all_fields

theorem ValiantBorder.contractingApproxRate {K : Type} [Field K] (hK : Paper.Contracting K)
    {G : ∀ S, MvPolynomial (Fin S × Fin S) K} {κ : ℕ} (hG : ValiantBorder.GridComplete K G κ) :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, Statement.Approximates (G m) s →
      (2 : ℝ) ^ (c * Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m)) < s := by sorry
