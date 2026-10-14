-- Prove2me | Theorems.Thm_SellingData_ListsBinary_proposition1_efficient_monotone
-- name    : SellingData.ListsBinary.proposition1_efficient_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:55.40124+00:00
-- url     : https://prove2.me/theorems/82bda102-e2ac-4721-8008-83f9fc194f34
-- title:
--   Proposition 1, p. 10 — the efficient informativeness α^e_i increases with c_i if φ < 1/2 and decreases if φ > 1/2
-- statement:
--   In the binary model of *Selling Data to Marketers*, call $a\in[\underline\alpha,\bar\alpha]$ **efficient** for weight $\theta_i>0$ and targeting cost $c$ if it maximizes the benchmark profit
--   $$\Pi_i(\alpha)=\theta_i\big[\sigma_h(\alpha)[v_h(\alpha)-c]-k(\alpha)\big]$$
--   over $[\underline\alpha,\bar\alpha]$. Let $c<c'$ be two targeting costs, both satisfying the standing assumption $v_l(\underline\alpha)<c,c'<v_h(\underline\alpha)$. Then:
--   1. if $\phi<1/2$, every efficient $a$ at $c$ and every efficient $a'$ at $c'$ satisfy $a\le a'$;
--   2. if $\phi>1/2$, every efficient $a$ at $c$ and every efficient $a'$ at $c'$ satisfy $a'\le a$.
--
--   In words: under the observable-cost benchmark, the efficient informativeness $\alpha^e_i$ increases with the targeting cost when the high value is unlikely and decreases when it is likely. Nothing is assumed about $k$ beyond the model ($k(\underline\alpha)=0$, increasing); in particular $k$ need not be convex.
--
--   **Formalization Note** "$\alpha^e_i$ increases with $c_i$" is stated for the whole set of maximizers, in the weak (Topkis) sense, since the maximizer need not be unique. The weight $\theta_i>0$ is arbitrary; it does not affect the maximizers.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 10, Proposition 1 (proof p. 31)

import Mathlib
import Definitions.Def_SellingData_ListsBinary_Setting

namespace SellingData.ListsBinary

/-- Proposition 1, p. 10: the efficient informativeness increases with the targeting cost if
`φ < 1/2` and decreases if `φ > 1/2` (every efficient point at the smaller cost lies weakly
below, resp. above, every efficient point at the larger cost). -/
theorem proposition1_efficient_monotone (M : Model) {θi c c' : ℝ} (hθi : 0 < θi)
    (hc : M.CostAdmissible c) (hc' : M.CostAdmissible c') (hcc' : c < c') :
    (M.phi < 1 / 2 → ∀ a a' : ℝ, M.IsEfficient θi c a → M.IsEfficient θi c' a' → a ≤ a') ∧
    (1 / 2 < M.phi → ∀ a a' : ℝ, M.IsEfficient θi c a → M.IsEfficient θi c' a' → a' ≤ a) := by sorry

end SellingData.ListsBinary
