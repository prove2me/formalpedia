-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_lemma_4_1
-- name    : ReflectedRWLDP.SamplePath.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:06.043012+00:00
-- url     : https://prove2.me/theorems/f3a935d5-ea95-4fc5-8203-d26baf8a9dcd
-- title:
--   Lemma 4.1 — $\mathcal B^*_y=0$ for $y\ge\bar y$, and $\mathcal B^*_y$ is attained over absolutely continuous paths
-- statement:
--   Let the reflected random walk satisfy the standing assumptions of the paper: i.i.d. increments with mean $\mu<0$, Assumptions 2.1–2.3, and $p>0$. Let $\mathcal B^*_y=\inf_{\xi\in B_y}I_y(\xi)$ be the value of the variational problem $(\mathcal B_y)$, let $\bar y=(|\mu|(p+1))^\alpha$, and let $B^{\mathbb{AC}}_y=B_y\cap\mathbb{AC}[0,\infty)$.
--
--   1. For every $y\ge\bar y$ there is a path $\xi^*\in B^{\mathbb{AC}}_y$ with $I_y(\xi^*)=0$, and $\mathcal B^*_y=0$.
--   2. For every $y\ge0$,
--   $$\mathcal B^*_y=\inf_{\xi\in B^{\mathbb{AC}}_y}I_y(\xi).$$
--
--   The infimum in $(\mathcal B_y)$ runs over all paths of bounded variation, with jumps and singular parts allowed. Part 2 says that restricting it to absolutely continuous paths does not change the value.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, p. 18, Lemma 4.1

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

/-- **Lemma 4.1** (p. 18). (i) For `y ≥ ȳ = (|µ|(p+1))^α` there is `ξ* ∈ B^{𝔸ℂ}_y` with `I_y(ξ*) = 0`,
and `B*_y = 0`. (ii) For `y ≥ 0`, `B*_y = inf_{ξ ∈ B^{𝔸ℂ}_y} I_y(ξ)`. -/
theorem lemma_4_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    (∀ y : ℝ, ybar P U p ≤ y →
      (∃ ξ ∈ BsetAC p y, rateI P U y ξ = 0) ∧ Bstar P U p y = 0) ∧
    ∀ y : ℝ, 0 ≤ y → Bstar P U p y = ⨅ ξ ∈ BsetAC p y, rateI P U y ξ := by sorry

end ReflectedRWLDP.SamplePath
