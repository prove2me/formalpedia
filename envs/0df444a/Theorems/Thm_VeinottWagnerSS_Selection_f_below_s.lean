-- Prove2me | Theorems.Thm_VeinottWagnerSS_Selection_f_below_s
-- name    : VeinottWagnerSS.Selection.f_below_s
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T14:05:03.478967+00:00
-- url     : https://prove2.me/theorems/e804b5c8-b56b-4d6a-9a1c-47a62fd5fddf
-- title:
--   §3, p. 533 — $f(x) = K + f(S)$ for $x < s$
-- statement:
--   Let $0 \le \alpha < 1$ and let $s \le S$ be integers. In the inventory model with set-up cost $K \ge 0$, one-period cost $G_\alpha$ (convex, $G_\alpha(y) \to \infty$ as $|y| \to \infty$) and i.i.d. integer demands with finite mean, let $f(x \mid s, S)$ be the expected total discounted cost of the stationary $(s, S)$ policy started at $X_1 = x$. If the initial stock is below the reorder point, $x < s$, then
--   $$f(x \mid s, S) = K + f(S \mid s, S).$$
--
--   Starting below $s$, the policy immediately orders up to $S$; the identity says that the cost of such a start is the set-up cost plus the cost of starting at $S$. In particular $a_\alpha(x \mid s, S) = (1-\alpha)f(x \mid s, S)$ is constant on $x < s$, which is what makes the function $\mathcal L_\alpha(S, D)$ of the paper well defined.
--
--   **Formalization Note** $f$ is the expected discounted cost of the $(s,S)$ Markov chain (definition `fCost`), not a formula; the model's standing assumptions are fields of `Model` although this identity does not use convexity or coercivity.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 533, §3, display after Eq. (9): f(x) = K + f(S), x < s

import Mathlib
import Definitions.Def_VeinottWagnerSS_Selection_Model

namespace VeinottWagnerSS.Selection

/-- Veinott & Wagner (1965), §3, p. 533: for `0 ≤ α < 1` and a stationary `(s, S)` policy
(`s ≤ S`), if `X₁ = x < s` then `f(x | s, S) = K + f(S | s, S)`. -/
theorem f_below_s (M : Model) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (s S : ℤ) (hsS : s ≤ S) (x : ℤ) (hx : x < s) :
    fCost M α s S x = M.K + fCost M α s S S := by sorry

end VeinottWagnerSS.Selection
