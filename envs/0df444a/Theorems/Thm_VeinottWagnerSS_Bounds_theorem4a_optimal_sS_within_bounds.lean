-- Prove2me | Theorems.Thm_VeinottWagnerSS_Bounds_theorem4a_optimal_sS_within_bounds
-- name    : VeinottWagnerSS.Bounds.theorem4a_optimal_sS_within_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T13:54:23.867981+00:00
-- url     : https://prove2.me/theorems/079959e2-c4a8-4f97-8e31-d469524e9884
-- title:
--   Theorem 4(a) — an optimal n-period (s, S) policy with $\underline{s} \le s_n \le \bar{s} \le \underline{S} \le S_n \le \bar{S}$
-- statement:
--   Consider the $n$-period periodic-review inventory model with backlogging: i.i.d. demands with distribution $\varphi$ on $\{0, 1, \dots\}$ of finite mean, set-up cost $K \ge 0$, discount factor $0 \le \alpha \le 1$, and one-period cost $G_\alpha : \mathbb Z \to \mathbb R$ that is convex on the integers with $G_\alpha(y) \to \infty$ as $|y| \to \infty$. The cost of a policy $Y$ from initial level $x$ is
--   $$f_n(x \mid Y) = \sum_{t=1}^{n} \alpha^{t-1}\bigl[K\,E\,\delta(Y_t - X_t) + E\,G_\alpha(Y_t)\bigr].$$
--   Let $\underline s, \bar s, \underline S, \bar S$ be the numbers defined by (21)–(23).
--
--   Then for every $n \ge 2$ there is a policy $Y^n$ such that
--
--   1. $Y^n$ is optimal: $f_n(x \mid Y^n) \le f_n(x \mid Y)$ for every admissible (history-dependent) policy $Y$ and every initial level $x$;
--   2. $Y^n$ is an $(s, S)$ policy, i.e. it uses an $(s_t, S_t)$ rule with $s_t \le S_t$ in each of the $n$ periods;
--   3. its first-period rule $(s_n, S_n)$ satisfies
--   $$\underline{s} \le s_n \le \bar{s} \le \underline{S} \le S_n \le \bar{S}.$$
--
--   The theorem localizes an optimal first-period policy of every finite-horizon model in a box computed from the one-period cost alone. The paper uses these bounds to restrict the search for optimal stationary policies.
--
--   **Formalization Note** The existence of an optimal $(s, S)$ policy, which the paper takes from Scarf and from Zabel (p. 529), is part of the conclusion, not a hypothesis. The model is the reduced model of Eq. (2): $G_\alpha$ is a primitive, and $f_n$ is valued in the extended reals.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 549, Theorem 4(a)

import Mathlib
import Definitions.Def_VeinottWagnerSS_Bounds_Model
import Definitions.Def_VeinottWagnerSS_Bounds_CriticalNumbers

open scoped ENNReal

namespace VeinottWagnerSS.Bounds

/-- Theorem 4(a), p. 549. For the `n`-period model (`n = 2, 3, ⋯`) there exists an optimal
`(s, S)` policy whose first-period rule `(s_n, S_n)` satisfies
`s̲ ≤ s_n ≤ s̄ ≤ S̲ ≤ S_n ≤ S̄`. Optimality is against every admissible (history-dependent)
policy and for every initial level `x`. -/
theorem theorem4a_optimal_sS_within_bounds (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (φ : PMF ℕ) (hμ : ∑' k : ℕ, (k : ℝ≥0∞) * φ k ≠ ⊤)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ (Y : Policy) (sn Sn : ℤ), IsOptimal φ G K α n Y ∧ IsSSPolicy n Y ∧
      sn ≤ Sn ∧ UsesRule Y 0 sn Sn ∧
      sLow G K ≤ sn ∧ sn ≤ sHigh G K α ∧ sHigh G K α ≤ SLow G ∧
      SLow G ≤ Sn ∧ Sn ≤ SHigh G K α := by sorry

end VeinottWagnerSS.Bounds
