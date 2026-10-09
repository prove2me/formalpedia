-- Prove2me | Theorems.Thm_SLQSolv_OpenNotClosed_eq_7_7
-- name    : SLQSolv.OpenNotClosed.eq_7_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:21:45.202987+00:00
-- url     : https://prove2.me/theorems/ba745244-c040-4535-995c-6ca83b6a99bd
-- title:
--   (7.7), p. 2306 — lim_{ε→0} ε/(ε + 2 − 2t) is 0 for t < 1 and 1 for t = 1
-- statement:
--   For $t\in[0,1]$ let $P_\varepsilon(t)=\varepsilon/(\varepsilon+2-2t)$ be the regularized Riccati solution (7.6). Then the limit as $\varepsilon\downarrow 0$ exists and
--
--   $$
--   P_0(t)\triangleq\lim_{\varepsilon\to0}P_\varepsilon(t)=\begin{cases}0,&0\le t<1,\\1,&t=1.\end{cases}
--   $$
--
--   Through Theorem 5.3 of the paper, $P_0(t)x^2$ is the value $V^0(t,x)$ of Example 7.1, which is therefore discontinuous at $t=1$.
--
--   **Formalization Note** The limit is taken along $\varepsilon\to0^+$, the values of $\varepsilon$ for which $P_\varepsilon$ is defined.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Example 7.1, (7.7), p. 2306

import Mathlib
import Definitions.Def_SLQSolv_OpenNotClosed_Examples

open MeasureTheory Set Filter Topology
open scoped NNReal Matrix

namespace SLQSolv.OpenNotClosed

/-- (7.7), p. 2306: `P₀(t) = lim_{ε→0} P_ε(t)` with `P_ε(t) = ε/(ε + 2 − 2t)` equals `0` for
`0 ≤ t < 1` and `1` for `t = 1`. -/
theorem eq_7_7 (t : ℝ≥0) (ht : t ≤ 1) :
    Tendsto (fun ε : ℝ => ε / (ε + 2 - 2 * (t : ℝ))) (𝓝[>] 0)
      (𝓝 (if t < 1 then 0 else 1)) := by sorry

end SLQSolv.OpenNotClosed
