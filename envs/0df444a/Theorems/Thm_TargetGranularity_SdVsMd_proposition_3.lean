-- Prove2me | Theorems.Thm_TargetGranularity_SdVsMd_proposition_3
-- name    : TargetGranularity.SdVsMd.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:05.924223+00:00
-- url     : https://prove2.me/theorems/4dacc440-807f-4949-872c-5b9e4b3bd91b
-- title:
--   Proposition 3, p. 21 (PDF 22) — for small c_ad and c_click just below c^max_click(c_ad, p), every sd equilibrium earns strictly more than every symmetric md equilibrium
-- statement:
--   Fix a price $p\in(0,1)$. There is $\delta>0$ such that for every unit ad cost $c_{ad}\in(0,\delta)$ there is $c_1<c^{max}_{click}(c_{ad},p)$ such that for every click cost $c_{click}>0$ with
--   $$c_1<c_{click}\le c^{max}_{click}(c_{ad},p)$$
--   (the threshold of Equation (7)):
--
--   1. a non-trivial sd equilibrium exists;
--   2. a non-trivial symmetric md equilibrium exists;
--   3. every non-trivial symmetric md equilibrium $\Sigma^{md}$ and every non-trivial sd equilibrium $\Sigma^{sd}$ satisfy
--   $$\Pi^{*md}<\Pi^{*sd}.$$
--
--   This is the paper's main result: more granular customer data can lower the firm's equilibrium profit. Under md targeting the firm targets a larger, more heterogeneous set of consumers, a targeted consumer is less sure that the product suits her, and fewer consumers click.
--
--   **Formalization Note** The page states the result for $c_{ad}<c^{max}_{ad}(p)$ and $c^{min}_{click}(c_{ad},p)<c_{click}\le c^{max}_{click}(c_{ad},p)$, where its proof defines $c^{min}_{click}$ as the least click cost with $\Pi^{*sd}\ge\Pi^{*md}$ and $c^{max}_{ad}$ as the root of $c^{min}_{click}=c^{max}_{click}$. Read literally that is nearly true by definition, so the statement is the region the proof constructs (p. 41): $\delta$ plays the role of $c^{max}_{ad}(p)$ and $c_1$ that of $c^{min}_{click}$, while the right end is the explicit $c^{max}_{click}$ of (7), included as on the page. The page's "the unique equilibrium" is rendered as existence plus a comparison of every pair of equilibria (uniqueness is in Propositions 1 and 2). Only symmetric md equilibria are compared, as on the page; with asymmetric ones the comparison can fail (p. 42).
-- source:
--   Despotakis & Yu, Multidimensional Targeting and Consumer Response, SSRN 3900394 (version of October 11, 2022), p. 21 (PDF 22), Proposition 3; proof, pp. 40–41 (PDF 41–42)

import Mathlib
import Definitions.Def_TargetGranularity_SdVsMd_Model

namespace TargetGranularity.SdVsMd

/-- Proposition 3, p. 21, in the form its proof establishes (p. 41): for every price `p ∈ (0,1)`
there is `δ > 0` such that for every `c_ad ∈ (0, δ)` there is `c₁ < c^max_click(c_ad, p)` such that
for every `c_click ∈ (c₁, c^max_click(c_ad, p)]` a non-trivial sd equilibrium and a non-trivial
symmetric md equilibrium exist, and every non-trivial symmetric md equilibrium earns strictly less
than every non-trivial sd equilibrium. -/
theorem proposition_3 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ cad : ℝ, 0 < cad → cad < δ →
      ∃ c₁ : ℝ, c₁ < cmaxClick cad p ∧
        ∀ cclick : ℝ, 0 < cclick → c₁ < cclick → cclick ≤ cmaxClick cad p →
          (∃ S : Set ℝ, IsSdEq p cad cclick S) ∧
          (∃ S : Set (ℝ × ℝ), IsSymMdEq p cad cclick S) ∧
          ∀ (Ssd : Set ℝ) (Smd : Set (ℝ × ℝ)), IsSdEq p cad cclick Ssd →
            IsSymMdEq p cad cclick Smd →
              mdProfit p cad cclick Smd < sdProfit p cad cclick Ssd := by sorry

end TargetGranularity.SdVsMd
