-- Prove2me | Theorems.Thm_VeinottWagnerSS_Bounds_lemma4_SLow_rule
-- name    : VeinottWagnerSS.Bounds.lemma4_SLow_rule
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T13:48:46.235062+00:00
-- url     : https://prove2.me/theorems/2a54e548-3e3b-4ca4-9f3a-c3d10c34f91b
-- title:
--   Lemma 4 — if $\bar{S} < S_n$ (and $s_n \le \bar s$), the rule $(s_n, \underline{S})$ in period 1 does at least as well
-- statement:
--   Consider the $n$-period inventory model with $n \ge 2$ under the standing assumptions ($0 \le \alpha \le 1$, $K \ge 0$, $\varphi$ with finite mean, $G_\alpha$ convex on $\mathbb Z$ with $G_\alpha(y) \to \infty$ as $|y| \to \infty$). Let $Y^n$ be an optimal policy which in period 1 uses the $(s_n, S_n)$ rule, with $s_n \le S_n$ and $s_n \le \bar s$. If
--   $$\bar{S} < S_n,$$
--   then there is an admissible policy $Y'$ that uses the $(s_n, \underline{S})$ rule in period 1 and satisfies
--   $$f_n(x \mid Y') \le f_n(x \mid Y^n) \qquad \text{for all integers } x.$$
--
--   Together with Lemma 3 this lets one move an optimal first-period rule into the box $s_n \le \bar s$, $S_n \le \bar S$ without losing optimality.
--
--   **Formalization Note** The hypothesis $s_n \le \bar s$ is not in the printed statement of Lemma 4. The paper's proof opens with "By lemma 3 we may assume that $s_n \le \bar s$", and without it the conclusion can fail: $(s_n, \underline S)$ is an $(s, S)$ rule only when $s_n \le \underline S$. For example, with $K = 0$ and $G_\alpha(y) = \max(0, -y, y - 5)$ one has $\bar s = \underline S = \bar S = 0$, and the policy ordering up to $3$ whenever the stock is below $3$ in every period is optimal with $(s_n, S_n) = (3, 3)$, while $(3, 0)$ is not a rule. The statement is therefore the lemma as its proof establishes it.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), pp. 548-549, Appendix §2, Lemma 4 (with the assumption s_n ≤ s̄ made at the start of its proof)

import Mathlib
import Definitions.Def_VeinottWagnerSS_Bounds_Model
import Definitions.Def_VeinottWagnerSS_Bounds_CriticalNumbers

open scoped ENNReal

namespace VeinottWagnerSS.Bounds

/-- Lemma 4, p. 548, in the form its proof establishes. Let `Y` (the paper's `Yⁿ`) be an optimal
policy for the `n`-period model (`n ≥ 2`) that uses the `(s_n, S_n)` rule in period 1, with
`s_n ≤ s̄` (the reduction "by lemma 3 we may assume that `s_n ≤ s̄`" of the paper's proof; without
it `(s_n, S̲)` need not be an `(s, S)` rule). If `S̄ < S_n`, then there is an admissible policy
`Y'` that uses the `(s_n, S̲)` rule in period 1 and satisfies `f_n(x | Y') ≤ f_n(x | Y)` for all
`x`. -/
theorem lemma4_SLow_rule (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (φ : PMF ℕ) (hμ : ∑' k : ℕ, (k : ℝ≥0∞) * φ k ≠ ⊤)
    (n : ℕ) (hn : 2 ≤ n)
    (Y : Policy) (sn Sn : ℤ) (hY : IsOptimal φ G K α n Y) (hsS : sn ≤ Sn)
    (hrule : UsesRule Y 0 sn Sn) (hs : sn ≤ sHigh G K α) (hlt : SHigh G K α < Sn) :
    ∃ Y' : Policy, Admissible Y' ∧ UsesRule Y' 0 sn (SLow G) ∧
      ∀ x : ℤ, cost φ G K α n x Y' ≤ cost φ G K α n x Y := by sorry

end VeinottWagnerSS.Bounds
