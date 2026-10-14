-- Prove2me | Theorems.Thm_SellingData_ListsRotation_proposition4_efficient_inverted_u
-- name    : SellingData.ListsRotation.proposition4_efficient_inverted_u
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:52.154442+00:00
-- url     : https://prove2.me/theorems/774941b1-d2f1-4a3d-88b6-df1dc3a79c42
-- title:
--   Proposition 4, p. 17 — the efficient informativeness $\alpha^e_i$ first increases and then decreases with $c_i$
-- statement:
--   In the rotation-order model, let $\theta_i>0$ and call $a$ **efficient at cost $c$** if it maximizes the benchmark objective
--   $$\Pi_i(\alpha,c)=\theta_i\Big[\int_c^{\bar v}(v-c)\,dH(v,\alpha)-k(\alpha)\Big]$$
--   over $\alpha\in[\underline\alpha,\bar\alpha]$. Then the efficient informativeness first increases and then decreases with the cost:
--
--   1. if $\underline v<c<c'\le v^+$, every efficient level at $c$ is at most every efficient level at $c'$;
--   2. if $v^+\le c<c'<\bar v$, every efficient level at $c'$ is at most every efficient level at $c$.
--
--   Thus the value of information is highest for costs near the rotation point $v^+$, giving an "inverted-U" relation between the targeting cost and the efficient informativeness. No convexity or differentiability of $k$ is assumed.
--
--   **Formalization Note** "Increases" and "decreases" are read in the sense of Topkis's theorem, which the paper's proof invokes: every maximizer at the larger cost is compared with every maximizer at the smaller one, since the maximizers need not be unique. The rotation point itself is included in both ranges.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 17, Proposition 4; proof p. 32

import Mathlib
import Definitions.Def_SellingData_ListsRotation_Setting

namespace SellingData.ListsRotation

/-- Proposition 4, p. 17 (proof p. 32): the efficient informativeness `α^e_i` first increases and
then decreases with `c_i` — increasing for costs up to the rotation point `v⁺` and decreasing
for costs from `v⁺` on. Every maximizer of (12) at the larger cost is compared with every
maximizer at the smaller cost. -/
theorem proposition4_efficient_inverted_u (M : Model) (θi : ℝ) (hθi : 0 < θi) :
    (∀ c c' : ℝ, M.vLo < c → c < c' → c' ≤ M.vPlus →
      ∀ a a' : ℝ, M.IsEfficient θi c a → M.IsEfficient θi c' a' → a ≤ a') ∧
    (∀ c c' : ℝ, M.vPlus ≤ c → c < c' → c' < M.vHi →
      ∀ a a' : ℝ, M.IsEfficient θi c a → M.IsEfficient θi c' a' → a' ≤ a) := by sorry

end SellingData.ListsRotation
