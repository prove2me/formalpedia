-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_lemma_4_1_ii
-- name    : ReflectedRWLDP.SamplePath.lemma_4_1_ii
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-03T20:44:42.28377+00:00
-- url     : https://prove2.me/theorems/547b0bac-7ca3-4f44-a9ce-3825781c1766
-- title:
--   Lemma 4.1 (ii), p. 18 — $\mathcal B^*_y=\inf_{\xi\in\mathbb B^{\mathbb{AC}}_y}I_y(\xi)$
-- statement:
--   Let $U_1,U_2,\dots$ satisfy the standing assumptions of the paper (i.i.d., $\mu=\mathbf E U<0$, Assumptions 2.1–2.3, $p>0$). Then for every $y\ge 0$ the optimal value of the variational problem $(\mathcal B_y)$ is attained in the limit by absolutely continuous paths:
--   $$\mathcal B^*_y=\inf_{\xi\in\mathbb B_y}I_y(\xi)=\inf_{\xi\in\mathbb B^{\mathbb{AC}}_y}I_y(\xi),$$
--   where $\mathbb B^{\mathbb{AC}}_y=\mathbb B_y\cap\mathbb{AC}[0,\infty)$.
--
--   This is part (ii) of Lemma 4.1; part (i) is `ReflectedRWLDP.SamplePath.lemma_4_1_i`. The paper's proof (§5.1) first removes downward singular parts using the monotonicity of the reflection map, then replaces the upward singular part by a steep linear segment of slope $y_\epsilon=-\mu\theta_+/\epsilon$ at the start of the path, using $\Lambda^*(x)\le(\theta_++\epsilon)x$ for $x\ge y_\epsilon$.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, p. 18, Lemma 4.1 (ii); proof pp. 26–27 (§5.1)

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

/-- **Lemma 4.1 (ii)** (p. 18). Under the standing assumptions, for every `y ≥ 0`,
`B*_y = inf_{ξ ∈ B^{𝔸ℂ}_y} I_y(ξ)`. -/
theorem lemma_4_1_ii {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    ∀ y : ℝ, 0 ≤ y → Bstar P U p y = ⨅ ξ ∈ BsetAC p y, rateI P U y ξ := by sorry

end ReflectedRWLDP.SamplePath
