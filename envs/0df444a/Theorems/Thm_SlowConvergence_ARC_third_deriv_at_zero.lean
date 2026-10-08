-- Prove2me | Theorems.Thm_SlowConvergence_ARC_third_deriv_at_zero
-- name    : SlowConvergence.ARC.third_deriv_at_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:21.201857+00:00
-- url     : https://prove2.me/theorems/83960e29-49b8-4cc1-ae6f-b49e3b15e79d
-- title:
--   §5, p. 15 — $|p_k^{(3)}(0)|\le 20$
-- statement:
--   Let $0<\tau<1$ and let $p_k$ be the Hermite pieces of the example. Then for every $k\ge0$
--   $$|p_k'''(0)| \le 20 .$$
--
--   The paper observes that on each interval the third derivative of $f_4$ is largest at the interval's first point, so this is the Lipschitz constant $L = 20$ of the plotted function.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 15, §5

import Mathlib
import Definitions.Def_SlowConvergence_ARC_Data
import Definitions.Def_SlowConvergence_ARC_Pieces

namespace SlowConvergence.ARC

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §5, p. 15: "(5.11) and (5.12) imply that |p'''(0)| ≤ 20".
For `0 < τ < 1` and every `k ≥ 0`, the third derivative of the Hermite piece `p_k` at the left end of its
interval satisfies `|p_k'''(0)| ≤ 20`. -/
theorem third_deriv_at_zero (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    |iteratedDeriv 3 (p τ k) 0| ≤ 20 := by sorry

end SlowConvergence.ARC
