-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_dM1_pseudoMetric
-- name    : ReflectedRWLDP.SamplePath.dM1_pseudoMetric
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-03T20:54:33.384323+00:00
-- url     : https://prove2.me/theorems/c5cf716d-c3fb-4c6f-9f41-b9ad52a18b81
-- title:
--   Definition 2.2, p. 6 — $d_{M_1'}$ on $\mathbb D[0,T]$ satisfies $d(\xi,\xi)=0$ and the triangle inequality
-- statement:
--   Fix $T>0$. For $\xi\in\mathbb D[0,T]$ let $\Gamma'(\xi)=\{(u,t)\in\mathbb R\times[0,T]:u\in[\xi(t-)\wedge\xi(t),\xi(t-)\vee\xi(t)]\}$ be its extended completed graph (with the convention $\xi(0-)=0$), ordered by $(u_1,t_1)<(u_2,t_2)$ iff $t_1<t_2$, or $t_1=t_2$ and $|\xi(t_1-)-u_1|<|\xi(t_2-)-u_2|$; let $\Pi'(\xi)$ be the set of its parametrizations, i.e. continuous nondecreasing maps $s\mapsto(u(s),t(s))$ of $[0,T]$ onto $\Gamma'(\xi)$. The $M_1'$ distance (Definition 2.2) is
--   $$d_{M_1'}(\xi,\zeta)=\inf_{(u,t)\in\Pi'(\xi),\ (v,r)\in\Pi'(\zeta)}\big\{\|u-v\|_\infty+\|t-r\|_\infty\big\}.$$
--   Then $d_{M_1'}$ is a pseudometric on $\mathbb D[0,T]$: for all $\xi,\zeta,\eta\in\mathbb D[0,T]$,
--   $$d_{M_1'}(\xi,\xi)=0,\qquad d_{M_1'}(\xi,\eta)\le d_{M_1'}(\xi,\zeta)+d_{M_1'}(\zeta,\eta).$$
--   (Symmetry is immediate from the definition.) The first identity says that every extended completed graph admits a parametrization; the triangle inequality rests on the fact that any two parametrizations of the same graph can be matched up to an arbitrarily small error.
--
--   The paper calls $d_{M_1'}$ the $M_1'$ metric; these are the metric properties used when transferring large deviation principles along exponentially equivalent sequences in the proof of Theorem 2.1.
--
--   **Formalization Note** Distances take values in $[0,\infty]$; an empty infimum would be $\infty$, so $d_{M_1'}(\xi,\xi)=0$ includes the existence of a parametrization.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, pp. 5–6, Definitions 2.1–2.2 (the M1′ metric); metric property as in Whitt (2002), Stochastic-Process Limits, §12.3 (Theorem 12.3.1) and §13.6.2 for M1′

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_MFGLimit_LDP_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_PathSpace
import Definitions.Def_ReflectedRWLDP_SamplePath_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_Model
import Definitions.Def_ReflectedRWLDP_SamplePath_RateFunction

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ReflectedRWLDP.SamplePath

/-- The `M₁′` distance of Definition 2.2 (p. 6) is a (pseudo)metric on `𝔻[0,T]`, `T > 0`: every path is at
distance `0` from itself (its extended completed graph admits a parametrization), and the triangle
inequality holds. -/
theorem dM1_pseudoMetric (T : ℝ) (hT : 0 < T) :
    (∀ ξ : DPath T, dM1 ξ ξ = 0) ∧
      ∀ ξ ζ η : DPath T, dM1 ξ η ≤ dM1 ξ ζ + dM1 ζ η := by sorry

end ReflectedRWLDP.SamplePath
