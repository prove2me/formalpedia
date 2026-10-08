-- Prove2me | Theorems.Thm_WhittFLT_TimeReversal_supDist_revTime
-- name    : WhittFLT.TimeReversal.supDist_revTime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:55.608714+00:00
-- url     : https://prove2.me/theorems/23b9b894-a3eb-450d-98ff-e5be5e66668f
-- title:
--   Uniform-distance bounds for time reversal
-- statement:
--   Let $x,y\in D$ and let $\rho$ be the uniform distance on $[0,1]$. For a complete separable additive metric group with translation-invariant metric,
--
--   $$
--   \rho(Rx,Ry)=\rho(x,y),\qquad
--   \rho(rx,ry)\le\rho(x,y)+m(x(1),y(1))\le 2\rho(x,y).
--   $$
--
--   These estimates quantify how each path reversal changes the uniform distance, before time changes enter the $J_1$ metric.
--
--   **Formalization Note** The Lean statement gives the two bounds on $\rho(rx,ry)$ separately. The endpoint condition $x(1)=x(1-)$ is included in $x,y\in D$. Distances are extended nonnegative reals, finite for these paths on $[0,1]$.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), §8, proof of Theorem 8.1, p. 84; https://doi.org/10.1287/moor.5.1.67

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Reversal

namespace WhittFLT.TimeReversal

open Set

/-- §8, proof of Theorem 8.1, p. 84: uniform-distance bounds for both reversals. -/
theorem supDist_revTime {S : Type*} [AddCommGroup S] [MetricSpace S] [CompleteSpace S]
    [TopologicalSpace.SeparableSpace S] (hinv : ∀ a b c : S, dist (a + c) (b + c) = dist a b)
    (x y : ℝ → S) (hx : InD x) (hy : InD y) :
    WhittFLT.Composition.supDist 0 1 (revTime x) (revTime y) = WhittFLT.Composition.supDist 0 1 x y ∧
      WhittFLT.Composition.supDist 0 1 (revTime0 x) (revTime0 y) ≤
        WhittFLT.Composition.supDist 0 1 x y + edist (x 1) (y 1) ∧
      WhittFLT.Composition.supDist 0 1 (revTime0 x) (revTime0 y) ≤ 2 * WhittFLT.Composition.supDist 0 1 x y := by sorry

end WhittFLT.TimeReversal
