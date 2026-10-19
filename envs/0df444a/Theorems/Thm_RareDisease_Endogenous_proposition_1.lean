-- Prove2me | Theorems.Thm_RareDisease_Endogenous_proposition_1
-- name    : RareDisease.Endogenous.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:07:10.725629+00:00
-- url     : https://prove2.me/theorems/d1b3c73f-4eae-4422-a9eb-9cf15d9627fc
-- title:
--   Proposition 1 — unique manufacturer-only subsidy under sales-based payment
-- statement:
--   Let $k>0$ be the R&D cost scale and $B>0$ the government's budget. Under manufacturer pricing and sales-based payment, define
--   $$
--   \alpha^*=\frac{1+128Bk-\sqrt{256Bk+1}}{128Bk}.
--   $$
--   The policy $(\alpha^*,0)$ is optimal, and every optimal policy equals it. At every manufacturer best response to this policy, government spending equals $B$, while patient welfare and manufacturer profit both equal
--   $$
--   W_A^*=\pi_A^*=\frac{2B}{\sqrt{256Bk+1}-1}.
--   $$
--   This identifies the unique subsidy allocation and confirms that the budget binds.
--
--   **Formalization Note** The paper implicitly requires $k>0$ and $B>0$ for the displayed formula. Optimality is an attained maximum over the full Stackelberg game, rather than an extremum of equation (13) taken as a definition.
-- source:
--   Olsder, Martagan, Tang, Improving Access to Rare Disease Treatments: Optimal Subsidies, Pricing, and Payment, SSRN working paper 3481150 (version of 2019-11-13), p. 12, §4.1, Proposition 1

import Mathlib
import Definitions.Def_RareDisease_Endogenous_Setting

namespace RareDisease.Endogenous

/-- Proposition 1, p. 12: unique sales-based optimum, binding budget, and equal
patient welfare and manufacturer profit. -/
theorem proposition_1 (k B : ℝ) (hk : 0 < k) (hB : 0 < B) :
    IsOptimalA k B (alphaStar k B) 0 ∧
    (∀ α β : ℝ, IsOptimalA k B α β ↔ α = alphaStar k B ∧ β = 0) ∧
    (∀ x ∈ BRA k (alphaStar k B) 0,
      spendA k (alphaStar k B) 0 x.1 x.2 = B ∧
      welfareA 0 x.1 x.2 = 2 * B / (Real.sqrt (256 * B * k + 1) - 1) ∧
      profitA k (alphaStar k B) 0 x.1 x.2 =
        2 * B / (Real.sqrt (256 * B * k + 1) - 1)) := by sorry

end RareDisease.Endogenous
