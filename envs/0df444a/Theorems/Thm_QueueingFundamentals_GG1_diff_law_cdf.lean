-- Prove2me | Theorems.Thm_QueueingFundamentals_GG1_diff_law_cdf
-- name    : QueueingFundamentals.GG1.diff_law_cdf
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T19:47:50.604629+00:00
-- url     : https://prove2.me/theorems/5b4dc850-15fd-4fce-a2c5-9f5638a0786b
-- title:
--   Eq. (6.9) — the CDF of U = S − T as a convolution
-- statement:
--   Let $A$ and $B$ be lifetime laws (the interarrival and service distributions), and let $U$ be the law of $S-T$ for independent $S\sim B$, $T\sim A$. Then for every real $x$,
--
--   $$
--   U(x)=\int_{\max(0,x)}^{\infty}B(y)\,dA(y-x),
--   $$
--
--   where $B(y)$ is the CDF of $B$ and $dA(y-x)$ denotes the law of $T+x$ in the variable $y$.
--
--   This is the formula through which the G/G/1 inputs $A$ and $B$ enter Lindley's equation.
--
--   **Formalization Note** The integral is over $[\max(0,x),\infty)$ with the endpoint included, against the image of $A$ under $a\mapsto a+x$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.285, Eq. (6.9)

import Mathlib
import Definitions.Def_QueueingFundamentals_GG1_Lindley

namespace QueueingFundamentals.GG1

open MeasureTheory

/-- Eq. (6.9) (p.285): for independent service time `S ~ B` and interarrival time `T ~ A`, the
CDF of `U = S − T` is `U(x) = ∫_{max(0,x)}^{∞} B(y) dA(y − x)`. The Stieltjes measure
`dA(y − x)` in `y` is the law of `T + x`, and the lower endpoint is included. -/
theorem diff_law_cdf (A B : Measure ℝ) (hA : IsLifetimeLaw A) (hB : IsLifetimeLaw B) (x : ℝ) :
    cdfOf (diffLaw A B) x =
      ∫ y in Set.Ici (max 0 x), cdfOf B y ∂(A.map (fun a => a + x)) := by sorry

end QueueingFundamentals.GG1
