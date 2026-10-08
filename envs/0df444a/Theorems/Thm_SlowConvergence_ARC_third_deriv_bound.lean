-- Prove2me | Theorems.Thm_SlowConvergence_ARC_third_deriv_bound
-- name    : SlowConvergence.ARC.third_deriv_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:43.313175+00:00
-- url     : https://prove2.me/theorems/f220ac38-6cc9-45a4-be02-0e87116a61c2
-- title:
--   §5, (5.12), p. 14 — $|p_k^{(3)}(t)|\le 452$ on $[0,s_k]$, uniformly in $k$
-- statement:
--   Let $0<\tau<1$ and let $p_k$ be the Hermite pieces of the example, used on $[0,s_k]$. Then
--   $$|p_k'''(t)| \le 452 \qquad\text{for all } k\ge0 \text{ and all } t\in[0,s_k].$$
--
--   A bound on the third derivative that does not depend on $k$ makes the second derivative of the glued function $f_4$ Lipschitz continuous with one constant on the whole half-line.
--
--   **Formalization Note** Only the two ends of the printed chain (5.12) are stated. The middle lines of (5.12) drop absolute values, and the factor $24\times13$ has no visible source; the end bound $452$ is nevertheless true (in fact $|p_k'''(t)|\le 6\cdot\tfrac{10}3 + 24\cdot5 + 60\cdot2 = 260$, since $|c_{3,k}|\le\tfrac{10}3$, $|c_{4,k}|s_k\le5$, $|c_{5,k}|s_k^2\le2$).
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 14, §5, (5.12)

import Mathlib
import Definitions.Def_SlowConvergence_ARC_Data
import Definitions.Def_SlowConvergence_ARC_Pieces

namespace SlowConvergence.ARC

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §5, (5.12), p. 14: the third derivative of the Hermite
piece `p_k` is bounded by 452 on `[0, s_k]`, uniformly in `k`: for `0 < τ < 1`, every `k ≥ 0` and every
`t ∈ [0, s_k]`, `|p_k'''(t)| ≤ 452`. (Only the two ends of the printed chain (5.12) are stated.) -/
theorem third_deriv_bound (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc 0 (sk τ k)) :
    |iteratedDeriv 3 (p τ k) t| ≤ 452 := by sorry

end SlowConvergence.ARC
