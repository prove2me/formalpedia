-- Prove2me | Theorems.Thm_RareDisease_Endogenous_proposition_1_outcome
-- name    : RareDisease.Endogenous.proposition_1_outcome
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:07:11.680965+00:00
-- url     : https://prove2.me/theorems/f5d0c47d-21d8-4c61-afe1-0a320e1315d5
-- title:
--   §4.2 — Proposition 1 persists under outcome-based payment
-- statement:
--   Let $k>0$, $B>0$, and $\alpha^*=(1+128Bk-\sqrt{256Bk+1})/(128Bk)$. In Setting (1B), with manufacturer pricing and outcome-based payment, $(\alpha^*,0)$ is optimal and is the only optimal subsidy policy. At every manufacturer best response to that policy, spending equals the budget $B$ and patient welfare and manufacturer profit are
--   $$
--   W_B^*=\pi_B^*=\frac{2B}{\sqrt{256Bk+1}-1}.
--   $$
--   This formalizes the paper's statement that Proposition 1 continues to hold for outcome-based payment.
--
--   **Formalization Note** The positivity assumptions make the closed form and best-response optimization nondegenerate. Efficacy ranges over all positive reals, matching the maximization in equation (8).
-- source:
--   Olsder, Martagan, Tang, Improving Access to Rare Disease Treatments: Optimal Subsidies, Pricing, and Payment, SSRN working paper 3481150 (version of 2019-11-13), p. 13, §4.2, paragraph after equation (16)

import Mathlib
import Definitions.Def_RareDisease_Endogenous_Setting

namespace RareDisease.Endogenous

/-- §4.2, p. 13, after (16): Proposition 1 continues to hold with outcome-based payment. -/
theorem proposition_1_outcome (k B : ℝ) (hk : 0 < k) (hB : 0 < B) :
    IsOptimalB k B (alphaStar k B) 0 ∧
    (∀ α β : ℝ, IsOptimalB k B α β ↔ α = alphaStar k B ∧ β = 0) ∧
    (∀ x ∈ BRB k (alphaStar k B) 0,
      spendB k (alphaStar k B) 0 x.1 x.2 = B ∧
      welfareB 0 x.1 x.2 = 2 * B / (Real.sqrt (256 * B * k + 1) - 1) ∧
      profitB k (alphaStar k B) 0 x.1 x.2 =
        2 * B / (Real.sqrt (256 * B * k + 1) - 1)) := by sorry

end RareDisease.Endogenous
