-- Prove2me | Theorems.Thm_VeinottWagnerSS_Selection_lemma1_optimalFor_accessible
-- name    : VeinottWagnerSS.Selection.lemma1_optimalFor_accessible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:10:20.061696+00:00
-- url     : https://prove2.me/theorems/929d182f-e16f-4b9f-9b70-db0aa7bb17f7
-- title:
--   Lemma 1 — an (s, S) policy optimal for $X_1 = x$ is optimal for every $x'$ accessible from $x$
-- statement:
--   Let $0 < \alpha < 1$. In the inventory model with set-up cost $K \ge 0$, convex one-period cost $G_\alpha$ with $G_\alpha(y) \to \infty$ as $|y| \to \infty$, and i.i.d. integer demands with finite mean, suppose the stationary $(s, S)$ policy ($s \le S$) is optimal for $X_1 = x$, that is,
--   $$a_\alpha(x \mid s, S) \le a_\alpha(x \mid \sigma, \Sigma) \qquad \text{for every } (\sigma, \Sigma) \text{ policy}, \ \sigma \le \Sigma.$$
--   If $x'$ is accessible from $x$ under $(s, S)$, i.e. $\Pr(X_t = x' \mid X_1 = x) > 0$ for some $t > 1$, then $(s, S)$ is also optimal for $X_1 = x'$:
--   $$a_\alpha(x' \mid s, S) \le a_\alpha(x' \mid \sigma, \Sigma) \qquad \text{for every } (\sigma, \Sigma) \text{ policy}.$$
--
--   Optimality at one starting stock therefore propagates along the paths of the policy's own stock process; this is the second ingredient of Theorem 2.
--
--   **Formalization Note** "Optimal" is among $(s, S)$ policies, as defined on p. 536. The lemma is true because, under the paper's standing assumptions, some stationary $(s, S)$ policy is optimal among **all** ordering policies (the existence result the paper cites in Section 2); the standing assumptions are therefore kept as fields of `Model`, and without them the statement can fail. The strict condition $\alpha > 0$ is the paper's.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 543, Lemma 1 (accessibility defined p. 542; proof Appendix §3, p. 551)

import Mathlib
import Definitions.Def_VeinottWagnerSS_Selection_Model

namespace VeinottWagnerSS.Selection

/-- Veinott & Wagner (1965), Lemma 1, p. 543: if `0 < α < 1` and the `(s, S)` policy is optimal
for `X₁ = x` (it minimizes `a_α(x | ·, ·)` over all `(s, S)` policies), then it is optimal for
every `x'` accessible from `x` under `(s, S)`. -/
theorem lemma1_optimalFor_accessible (M : Model) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (s S x : ℤ) (hopt : OptimalFor M α {x} s S) (x' : ℤ) (hacc : Accessible M s S x x') :
    OptimalFor M α {x'} s S := by sorry

end VeinottWagnerSS.Selection
