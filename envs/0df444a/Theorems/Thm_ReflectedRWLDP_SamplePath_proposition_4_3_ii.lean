-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_proposition_4_3_ii
-- name    : ReflectedRWLDP.SamplePath.proposition_4_3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:20.573441+00:00
-- url     : https://prove2.me/theorems/5501780d-7f87-4553-8f43-d0f3a407cf5c
-- title:
--   Proposition 4.3 (ii) — $\mathcal B^*_0=\mathcal B^*_\pi$
-- statement:
--   Under the standing assumptions (i.i.d. increments with mean $\mu<0$, Assumptions 2.1–2.3, $p>0$), let $\beta=\sup\{\theta\ge0:\mathbf E(e^{\theta U})\le1\}$ be the decay rate of the stationary distribution of the reflected random walk. The value of $(\mathcal B_y)$ at $y=0$ equals the value of $(\mathcal B_\pi)$:
--   $$\mathcal B^*_0=\mathcal B^*_\pi=\inf_{y\in[0,\infty),\ \xi\in B_y}\{\beta y+I_y(\xi)\}.$$
--
--   Consequently the busy period in progress at the end of the time horizon has the same tail asymptotics as a busy period started from $0$ (Theorem 2.3).
--
--   **Formalization Note** Only part (ii) of Proposition 4.3 is formalized. $\beta$ and all values lie in $[0,\infty]$.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, p. 20, Proposition 4.3 (ii)

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

/-- **Proposition 4.3 (ii)** (p. 20). `B*₀ = B*_π`. -/
theorem proposition_4_3_ii {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    Bstar P U p 0 = BstarPi P U p := by sorry

end ReflectedRWLDP.SamplePath
