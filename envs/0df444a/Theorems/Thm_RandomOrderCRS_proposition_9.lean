-- Prove2me | Theorems.Thm_RandomOrderCRS_proposition_9
-- name    : RandomOrderCRS.proposition_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:09.031183+00:00
-- url     : https://prove2.me/theorems/dd4fa6d7-1e90-4ae3-934b-74e83bc21b6b
-- title:
--   Proposition 9 — second-order minimization property of $a_1$
-- statement:
--   For $a=a_1$ and $x\in[0,1)$,
--
--   $$\frac{a'(x)}{a(x)}+\frac4{1-x}-\frac{2(1-\exp(x-1))}{\exp(x-1)-x}\le0.$$
--
--   Equality holds at $x=0$. This is the property that makes a single neighbour the worst case in Lemma 3.
--
--   Differences from the source:
--   - encoding: for all $x\in[0,1]$ → for all $x\in[0,1)$; reason: the printed expression is $0/0$ at $x=1$, and the argument needs only the points below 1
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, Proposition 9, p.20; §C.5, ec17

import Mathlib
import Definitions.Def_RandomOrderCRS_Attenuation

open Real

namespace RandomOrderCRS

/-- Proposition 9 (Second-order minimization), MacRury, Ma & Grammel, arXiv:2209.07520v2, p.20, for
`a = a₁`: `a′(x)/a(x) + 4/(1 − x) − 2(1 − exp(x − 1))/(exp(x − 1) − x) ≤ 0`.

**Formalization Note.** Stated on `[0, 1)`. The paper prints `x ∈ [0, 1]`, but the expression is
`0/0` at `x = 1`, and its use in the proof of Lemma 3 (ec16–ec17) needs only `z_h > 0`. -/
theorem proposition_9 :
    ∀ t ∈ Set.Ico (0 : ℝ) 1,
      deriv a₁ t / a₁ t + 4 / (1 - t) - 2 * (1 - exp (t - 1)) / (exp (t - 1) - t) ≤ 0 := by sorry

end RandomOrderCRS
