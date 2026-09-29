-- Prove2me | Theorems.Thm_RealInequalities_sqrt_log_lt_rpow_one_sub
-- name    : RealInequalities.sqrt_log_lt_rpow_one_sub
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:57:46.63281+00:00
-- url     : https://prove2.me/theorems/13a8a398-03f7-4786-a152-f501b6494d4c
-- title:
--   Comparing two real powers of $\log X$
-- statement:
--   **A strict comparison of real powers of a quantity exceeding one.**
--
--   If $\log X > 1$ and $\theta < 1/2$, then
--
--   $$(\log X)^{1/2} \;<\; (\log X)^{\,1-\theta}.$$
--
--   For a base $t > 1$ the map $\alpha \mapsto t^{\alpha}$ is strictly increasing, so the inequality
--   reduces to comparing exponents: $\theta < 1/2$ is equivalent to $1 - \theta > 1/2$. Both
--   hypotheses are needed — for a base in $(0,1)$ the map is *decreasing* and the inequality would
--   reverse, which is why $\log X > 1$ rather than merely $\log X > 0$ is assumed.
--
--   Comparisons of this kind appear when an error term of size $(\log X)^{1/2}$ must be absorbed
--   into a main term of size $(\log X)^{1-\theta}$, as in zero-free-region and exponential-sum
--   arguments where $\theta$ is a parameter shrinking as the range grows. The strictness is what
--   allows the absorption to leave room for a further factor.
--
--   **Formalization note.** Powers are `Real.rpow`, so real exponents are allowed and the base is
--   required positive; $\log X > 1$ supplies that and more.
-- source:
--   Elementary. Lean proof extracted from `Salt/MR/` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace RealInequalities

theorem sqrt_log_lt_rpow_one_sub (X θ : ℝ) (hX : 1 < Real.log X) (hθ : θ < 1 / 2) :
    (Real.log X) ^ ((1 : ℝ) / 2) < (Real.log X) ^ (1 - θ) := by sorry

end RealInequalities
