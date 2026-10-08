-- Prove2me | Theorems.Thm_QueueingFundamentals_GG1_one_step_convolution
-- name    : QueueingFundamentals.GG1.one_step_convolution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T19:48:01.08673+00:00
-- url     : https://prove2.me/theorems/e730604c-141b-4594-bf56-75937eb2e738
-- title:
--   The one-step convolution of Lindley's recursion (p.285)
-- statement:
--   In the G/G/1 queue let the line delay $W_q^{(n)}$ of the $n$th customer have a distribution $\nu$ on $[0,\infty)$ with CDF $W_q^{(n)}(t)$, independent of the service time $S^{(n)}\sim B$ and the interarrival time $T^{(n)}\sim A$, which are themselves independent lifetime laws. Let $U^{(n)}$ be the law of $S^{(n)}-T^{(n)}$. Then the delay $W_q^{(n+1)}=\max(0,W_q^{(n)}+S^{(n)}-T^{(n)})$ of the next customer has CDF
--
--   $$
--   W_q^{(n+1)}(t)=\int_{-\infty}^{t}W_q^{(n)}(t-x)\,dU^{(n)}(x)\qquad(0\le t<\infty).
--   $$
--
--   Applied to a stationary delay distribution this gives Lindley's equation (6.8).
--
--   **Formalization Note** The law of $W_q^{(n+1)}$ is `lindleyStep (diffLaw A B) ν`; the integral runs over $(-\infty,t]$, endpoint included.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.284–285, §6.2, the unnumbered convolution formula for W_q^{(n+1)}(t) on p.285

import Mathlib
import Definitions.Def_QueueingFundamentals_GG1_Lindley

namespace QueueingFundamentals.GG1

open MeasureTheory

/-- The one-step convolution (p.285): if the delay `W_q^{(n)}` of the `n`th customer has law `ν`
on `[0, ∞)` and is independent of `U^{(n)} = S^{(n)} − T^{(n)}` (with `S^{(n)} ~ B`, `T^{(n)} ~ A`
independent), then the delay `W_q^{(n+1)} = max(0, W_q^{(n)} + U^{(n)})` of the next customer has
CDF `W_q^{(n+1)}(t) = ∫_{−∞}^{t} W_q^{(n)}(t − x) dU^{(n)}(x)` for `0 ≤ t < ∞`. -/
theorem one_step_convolution (A B ν : Measure ℝ) (hA : IsLifetimeLaw A) (hB : IsLifetimeLaw B)
    (hν : IsLifetimeLaw ν) (t : ℝ) (ht : 0 ≤ t) :
    cdfOf (lindleyStep (diffLaw A B) ν) t =
      ∫ x in Set.Iic t, cdfOf ν (t - x) ∂(diffLaw A B) := by sorry

end QueueingFundamentals.GG1
