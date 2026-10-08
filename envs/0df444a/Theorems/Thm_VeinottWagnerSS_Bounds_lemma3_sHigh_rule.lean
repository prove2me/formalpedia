-- Prove2me | Theorems.Thm_VeinottWagnerSS_Bounds_lemma3_sHigh_rule
-- name    : VeinottWagnerSS.Bounds.lemma3_sHigh_rule
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T13:43:49.291477+00:00
-- url     : https://prove2.me/theorems/33bab586-802b-44bb-bb5d-ee158615e0d2
-- title:
--   Lemma 3 — if $\bar{s} < s_n$, the rule $(\bar{s}, S_n)$ in period 1 does at least as well
-- statement:
--   Consider the $n$-period inventory model with $n \ge 2$ under the standing assumptions ($0 \le \alpha \le 1$, $K \ge 0$, $\varphi$ with finite mean, $G_\alpha$ convex on $\mathbb Z$ with $G_\alpha(y) \to \infty$ as $|y| \to \infty$). Let $Y^n$ be an optimal policy which in period 1 uses the $(s_n, S_n)$ rule, $s_n \le S_n$. If
--   $$\bar{s} < s_n,$$
--   then there is an admissible policy $Y'$ that uses the $(\bar{s}, S_n)$ rule in period 1 and satisfies
--   $$f_n(x \mid Y') \le f_n(x \mid Y^n) \qquad \text{for all integers } x.$$
--
--   Consequently $Y'$ is again optimal, so one may always assume $s_n \le \bar s$.
--
--   **Formalization Note** "Policy" means an admissible history-dependent policy of the model definition; $f_n$ is the extended-real cost of Eq. (2).
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 548, Appendix §2, Lemma 3

import Mathlib
import Definitions.Def_VeinottWagnerSS_Bounds_Model
import Definitions.Def_VeinottWagnerSS_Bounds_CriticalNumbers

open scoped ENNReal

namespace VeinottWagnerSS.Bounds

/-- Lemma 3, p. 548. Let `Y` (the paper's `Yⁿ`) be an optimal policy for the `n`-period model
(`n ≥ 2`) that uses the `(s_n, S_n)` rule (`s_n ≤ S_n`) in period 1. If `s̄ < s_n`, then there is
an admissible policy `Y'` that uses the `(s̄, S_n)` rule in period 1 and satisfies
`f_n(x | Y') ≤ f_n(x | Y)` for all `x`. -/
theorem lemma3_sHigh_rule (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (φ : PMF ℕ) (hμ : ∑' k : ℕ, (k : ℝ≥0∞) * φ k ≠ ⊤)
    (n : ℕ) (hn : 2 ≤ n)
    (Y : Policy) (sn Sn : ℤ) (hY : IsOptimal φ G K α n Y) (hsS : sn ≤ Sn)
    (hrule : UsesRule Y 0 sn Sn) (hlt : sHigh G K α < sn) :
    ∃ Y' : Policy, Admissible Y' ∧ UsesRule Y' 0 (sHigh G K α) Sn ∧
      ∀ x : ℤ, cost φ G K α n x Y' ≤ cost φ G K α n x Y := by sorry

end VeinottWagnerSS.Bounds
