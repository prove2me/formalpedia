-- Prove2me | Theorems.Thm_SellingData_AppendsBinary_proposition3_appends_distortion
-- name    : SellingData.AppendsBinary.proposition3_appends_distortion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:37.618007+00:00
-- url     : https://prove2.me/theorems/77f1cd3e-3c31-45a1-9c13-2ea8e0a60d00
-- title:
--   Proposition 3, p. 13 — data appends with c_L < c_H < û: α*_H = α^e_H; α*_L < α^e_L if φ < 1/2 and α*_L > α^e_L if φ > 1/2
-- statement:
--   Consider a monopoly data seller who sells data appends to marketers with privately known targeting costs $c_L<c_H$, in the binary model with prior $\varphi\in(0,1)$, and suppose
--   $$c_L<c_H<\hat u=\varphi\bar u+(1-\varphi)\underline u .$$
--   Suppose further that the selling cost $k$ is continuous on $[\underline\alpha,\bar\alpha]$ and differentiable on $(\underline\alpha,\bar\alpha)$, with $k'(\underline\alpha)=0$ (right derivative) and $k'(\alpha)\to+\infty$ as $\alpha\to\bar\alpha^-$. Then:
--
--   1. **The high-cost plan is efficient.** A value $a$ is the high-cost informativeness $\alpha_H^*$ of some optimal menu if and only if it is an efficient informativeness $\alpha_H^e$, i.e. a maximizer of the benchmark profit (4) at cost $c_H$.
--   2. **If $\varphi<1/2$, the low-cost plan is under-informative:** for every optimal menu and every efficient $\alpha_L^e$, $\alpha_L^*<\alpha_L^e$.
--   3. **If $\varphi>1/2$, the low-cost plan is over-informative:** for every optimal menu and every efficient $\alpha_L^e$, $\alpha_L^*>\alpha_L^e$.
--
--   This is the "double mirror image" of the marketing-list result: with data appends and costs below the prior mean the high-cost marketers are the high type, so it is the low-cost plan that is distorted, and the direction of the distortion is reversed.
--
--   **Formalization Note** Optimal menus are maximizers of the data-append screening problem itself ((6) with $IR_i$ replaced by $U_{ii}\ge\max\{\hat u-c_i,0\}$), not of the reduced problem (8). Since neither optimum need be unique, "$\alpha_H^*=\alpha_H^e$" is stated as equality of the two sets of maximizers and the strict inequalities hold for every pair of maximizers. The regularity of $k$ is the part of footnote 5 (p. 7) that makes the efficient low-cost informativeness interior; convexity and twice differentiability, which footnote 5 also mentions, are not assumed.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 13, Proposition 3; proof pp. 31–32; footnote 5, p. 7

import Mathlib
import Definitions.Def_SellingData_AppendsBinary_Setting

namespace SellingData.AppendsBinary

open Model Filter Topology

/-- Proposition 3, p. 13: in selling data appends with `c_L < c_H < û`, the informativeness of the
high-cost plan is efficient (the high-cost informativeness levels of optimal menus are exactly the
maximizers of (4) at `c_H`), and every optimal low-cost informativeness is strictly below every
efficient one if `φ < 1/2`, strictly above if `φ > 1/2`. The regularity of `k` is footnote 5's
`k′(α̲) = 0`, `k′(ᾱ) = +∞`. -/
theorem proposition3_appends_distortion (M : Model) (hcH : M.cH < M.uHat)
    (hk_cont : ContinuousOn M.k (Set.Icc M.aLo M.aHi))
    (hk_diff : ∀ a ∈ Set.Ioo M.aLo M.aHi, DifferentiableAt ℝ M.k a)
    (hk_lo : HasDerivWithinAt M.k 0 (Set.Ici M.aLo) M.aLo)
    (hk_hi : Tendsto (deriv M.k) (𝓝[<] M.aHi) atTop) :
    (∀ a : ℝ, (∃ m : Menu, M.IsOptimalMenu m ∧ m.αH = a) ↔ M.IsEfficient SellingData.ListsBinary.CostType.H a) ∧
      (M.φ < 1 / 2 → ∀ m : Menu, M.IsOptimalMenu m →
        ∀ a : ℝ, M.IsEfficient SellingData.ListsBinary.CostType.L a → m.αL < a) ∧
      (1 / 2 < M.φ → ∀ m : Menu, M.IsOptimalMenu m →
        ∀ a : ℝ, M.IsEfficient SellingData.ListsBinary.CostType.L a → a < m.αL) := by sorry

end SellingData.AppendsBinary
