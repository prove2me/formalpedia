-- Prove2me | Theorems.Thm_RareDisease_Endogenous_corollary_1
-- name    : RareDisease.Endogenous.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:07:18.985028+00:00
-- url     : https://prove2.me/theorems/0cab7410-5d04-44c1-a9f5-8a9eebdc4614
-- title:
--   Corollary 1 — subsidy budget determines which payment scheme has the lower price
-- statement:
--   Let $k>0$ be the R&D cost scale and $B>0$ the subsidy budget. The policy $(\alpha^*,0)$, where $\alpha^*=(1+128Bk-\sqrt{256Bk+1})/(128Bk)$, is optimal under both sales-based and outcome-based payment, so optimal policies exist in both schemes. For every optimal policy in each scheme and every associated manufacturer best response, write $p_A$ and $p_B$ for the sales-based and outcome-based prices. Then
--   $$
--   B<k-\frac18\;\Longrightarrow\;p_A<p_B,\qquad
--   B=k-\frac18\;\Longrightarrow\;p_A=p_B,\qquad
--   B>k-\frac18\;\Longrightarrow\;p_A>p_B.
--   $$
--   This compares actual optimal prices in the two games, including the threshold case.
--
--   **Formalization Note** Corollary 1(2) prints a strict “higher price” claim for $B\ge k-1/8$. At equality the prices coincide, so the formal statement corrects that boundary slip. The paper's unconstrained efficacy choice $e>0$ is retained; $e^*$ can exceed one in the high-budget regime.
-- source:
--   Olsder, Martagan, Tang, Improving Access to Rare Disease Treatments: Optimal Subsidies, Pricing, and Payment, SSRN working paper 3481150 (version of 2019-11-13), p. 13, §4.2, Corollary 1, and p. 14, paragraph after it

import Mathlib
import Definitions.Def_RareDisease_Endogenous_Setting

namespace RareDisease.Endogenous

/-- Corollary 1, pp. 13–14, with the equality case corrected. -/
theorem corollary_1 (k B : ℝ) (hk : 0 < k) (hB : 0 < B) :
    IsOptimalA k B (alphaStar k B) 0 ∧
    IsOptimalB k B (alphaStar k B) 0 ∧
    ∀ α β α' β' : ℝ, IsOptimalA k B α β → IsOptimalB k B α' β' →
      ∀ x ∈ BRA k α β, ∀ y ∈ BRB k α' β',
        (B < k - 1 / 8 → x.1 < y.1) ∧
        (k - 1 / 8 < B → y.1 < x.1) ∧
        (B = k - 1 / 8 → x.1 = y.1) := by sorry

end RareDisease.Endogenous
