-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_lemma_4_4
-- name    : ReflectedRWLDP.SamplePath.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:29.059964+00:00
-- url     : https://prove2.me/theorems/1091b440-ea98-4325-8aec-521448c5a6cf
-- title:
--   Lemma 4.4 — $\mathcal B^*_y=\mathcal V^{T*}_y$ for every horizon $T\ge M$, with $M$ the constant of Lemma 4.3
-- statement:
--   Under the standing assumptions (i.i.d. increments with mean $\mu<0$, Assumptions 2.1–2.3, $p>0$), let $\mathcal B^*_y$ be the value of $(\mathcal B_y)$, $I_y$ its cost, $B^{\mathbb{AC}}_y$ the absolutely continuous paths of $B_y$, $\mathcal T(\xi)$ the exit time, and $\mathcal V^{T*}_y$ the value of the finite-horizon problem $(\mathcal V^T_y)$. For $M>0$ let $B^{\mathbb{AC};M}_y=B^{\mathbb{AC}}_y\cap\{\xi:\mathcal T(\xi)\le M\}$. Fix $y\ge0$ and let $M>0$ be a constant as in Lemma 4.3, that is, one for which
--   $$\inf_{\xi\in B^{\mathbb{AC}}_y}I_y(\xi)=\inf_{\xi\in B^{\mathbb{AC};M}_y}I_y(\xi).\qquad(4.4)$$
--   Then
--   $$\mathcal B^*_y=\mathcal V^{T*}_y\qquad\text{for every }T\ge M .$$
--
--   This lets the area over the random busy period be replaced by the area over a large fixed horizon.
--
--   **Formalization Note** The paper takes $M$ to be "the constant in Lemma 4.3", which is not formalized in this mission. Lemma 4.3 asserts, for each $y\ge0$, the existence of $M=M(y)>0$ with (i) every $\xi\in B^{\mathbb{AC}}_y$ is dominated in cost by some $\zeta\in B^{\mathbb{AC};M}_y$, (ii) the identity (4.4), and (iii) a linear growth bound on $y\mapsto M(y)$. The statement takes $M$ as a hypothesis carrying (4.4), the property the paper's proof of Lemma 4.4 (§5.5, Claim 2) invokes; (i) implies (4.4), and (iii) concerns the dependence on $y$, not a single $y$.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, p. 22, Lemma 4.4 (with the constant M of Lemma 4.3, characterized by (4.4))

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

/-- **Lemma 4.4** (p. 22). Let `y ≥ 0` and let `M > 0` be a constant as in Lemma 4.3, i.e. one for which
(4.4) holds: `inf_{ξ ∈ B^{𝔸ℂ}_y} I_y(ξ) = inf_{ξ ∈ B^{𝔸ℂ;M}_y} I_y(ξ)`, where
`B^{𝔸ℂ;M}_y = B^{𝔸ℂ}_y ∩ {ξ : 𝒯(ξ) ≤ M}` (p. 22). Then `B*_y = 𝒱^{T*}_y` for every `T ≥ M`. -/
theorem lemma_4_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) (y : ℝ) (hy : 0 ≤ y) (M : ℝ) (hM : 0 < M)
    (hM43 : (⨅ ξ ∈ BsetAC p y, rateI P U y ξ) =
      ⨅ ξ ∈ BsetAC p y ∩ {ξ | exitTime ξ ≤ ENNReal.ofReal M}, rateI P U y ξ) :
    ∀ T : ℝ, M ≤ T → Bstar P U p y = VTstar P U p T y := by sorry

end ReflectedRWLDP.SamplePath
