-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_lemma_4_1_i
-- name    : ReflectedRWLDP.SamplePath.lemma_4_1_i
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-03T20:44:58.845934+00:00
-- url     : https://prove2.me/theorems/1e8fc309-ffa6-44e0-93ef-6f2866246baf
-- title:
--   Lemma 4.1 (i), p. 18 — for $y\ge\bar y$ there is a zero-cost path in $\mathbb B^{\mathbb{AC}}_y$ and $\mathcal B^*_y=0$
-- statement:
--   Let $U_1,U_2,\dots$ satisfy the standing assumptions of the paper (i.i.d., $\mu=\mathbf E U<0$, Assumptions 2.1–2.3, $p>0$), let $\alpha=1/(1+p)$ and $\bar y=(|\mu|(p+1))^{\alpha}$. Then for every $y\ge\bar y$ there exists an absolutely continuous path $\xi^*\in\mathbb B^{\mathbb{AC}}_y=\mathbb B_y\cap\mathbb{AC}[0,\infty)$ with $I_y(\xi^*)=0$, and consequently the optimal value of the variational problem $(\mathcal B_y)$ is
--   $$\mathcal B^*_y=\inf_{\xi\in\mathbb B_y}I_y(\xi)=0.$$
--   Here $\mathbb B_y$ is the set of paths $\xi\in\mathbb{BV}[0,\infty)$ with $\xi(0)=y$ and $\int_0^{\mathcal T(\xi)}\Psi(\xi)(s)^p\,ds\ge1$, where $\Psi$ is the reflection map and $\mathcal T(\xi)$ the first time $\Psi(\xi)$ returns to $0$. (The witness in the paper is the fluid path $\xi^*(t)=y+\mu t$.)
--
--   This is part (i) of Lemma 4.1; part (ii) is `ReflectedRWLDP.SamplePath.lemma_4_1_ii`.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, p. 18, Lemma 4.1 (i); proof p. 26 (§5.1)

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

/-- **Lemma 4.1 (i)** (p. 18). Under the standing assumptions, for every `y ≥ ȳ = (|µ|(p+1))^α` there
is a path `ξ* ∈ B^{𝔸ℂ}_y` with `I_y(ξ*) = 0`, and `B*_y = 0`. -/
theorem lemma_4_1_i {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    ∀ y : ℝ, ybar P U p ≤ y →
      (∃ ξ ∈ BsetAC p y, rateI P U y ξ = 0) ∧ Bstar P U p y = 0 := by sorry

end ReflectedRWLDP.SamplePath
