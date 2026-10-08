-- Prove2me | Theorems.Thm_WagelmansELS_Efficient_ordered_ratios
-- name    : WagelmansELS.Efficient.ordered_ratios
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:59:52.054707+00:00
-- url     : https://prove2.me/theorems/8fb5afde-3772-4606-8589-9df331f25e1c
-- title:
--   Section 2: consecutive lower-envelope ratios are strictly ordered
-- statement:
--   Let $1\le i\le n$. If $t,t'\in E_i$, $t'=\operatorname{succ}_i(t)$, and $t'<n+1$, then the slopes between these and the next efficient point satisfy
--   $$r_i(t)>r_i(t').$$
--
--   This is the finite-point content of the paper's claim that the lower envelope is piecewise linear and convex: at each interior breakpoint its slope changes. It is the ordering used by the threshold selector.
--
--   **Formalization Note** Abscissae decrease as period indexes increase, so the inequality points in this direction. Interior collinear points are excluded from $E_i$.
-- source:
--   Wagelmans, Van Hoesel and Kolen, Economic Lot Sizing, Oper. Res. 40 Supp. 1 (1992), p. S147, Section 2, sentence “Furthermore, it is clear that g is a piecewise linear convex function”; p. S149, ordered ratios

import Mathlib
import Definitions.Def_WagelmansELS_Efficient_ThresholdRule

namespace WagelmansELS.Efficient

/-- Section 2, pp. S147, S149: consecutive slopes of the polygonal lower envelope
are strictly ordered at its breakpoints. -/
theorem ordered_ratios (P : Instance) (i t t' : ℕ)
    (hi : 1 ≤ i) (hin : i ≤ P.n)
    (ht : t ∈ P.E i) (ht' : t' ∈ P.E i)
    (hs : t' = P.succ i t) (hnext : t' < P.n + 1) :
    P.ratio i t > P.ratio i t' := by sorry

end WagelmansELS.Efficient
