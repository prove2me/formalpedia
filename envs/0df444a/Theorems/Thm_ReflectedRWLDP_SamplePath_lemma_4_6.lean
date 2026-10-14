-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_lemma_4_6
-- name    : ReflectedRWLDP.SamplePath.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:23.616405+00:00
-- url     : https://prove2.me/theorems/5e527d78-fdf1-4b11-9b95-aa2357ceae19
-- title:
--   Lemma 4.6 — exponential bounds for $\mathbf P_{xy}(T_1/x>T)$ and for the area over a fixed horizon
-- statement:
--   Under the standing assumptions (i.i.d. increments with mean $\mu<0$, Assumptions 2.1–2.3, $p>0$), let $\mathbf P_{xy}$ be the law of the reflected random walk started at $X_0=xy$, and let $T_1=\inf\{k>0:X_k=0\}$ be its first return time to $0$. Limits are taken as $x\to\infty$ over the reals.
--
--   1. For every $t,y\ge0$ and $T>0$,
--   $$\limsup_{x\to\infty}\frac1x\log\mathbf P_{xy}(T_1/x>T)\le ty+T\log\mathbf Ee^{tU}.$$
--   2. For every $y\ge0$ and $T>0$,
--   $$\limsup_{x\to\infty}\frac1x\log\mathbf P_{xy}\Big(\int_0^T(X_{\lfloor sx\rfloor}/x)^p\,ds\ge1\Big)\le-\mathcal V^{T*}_y .$$
--
--   These two bounds combine, through Lemma 4.4, into the upper bound of Proposition 4.2.
--
--   **Formalization Note** $\log\mathbf Ee^{tU}$ is `logMGF` and may be $+\infty$, in which case part 1 holds trivially. Logarithms and limits superior are taken in the extended reals. The event $T_1/x>T$ is written $xT<T_1$ with $T_1\in\mathbb N\cup\{\infty\}$. The integral is a lower Lebesgue integral of a nonnegative step function.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, pp. 22–23, Lemma 4.6, (4.5)–(4.6)

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

/-- **Lemma 4.6** (pp. 22–23). For the chain `X` started at `X₀ = xy` (law `P_{xy}`) with first return time
`T₁`: (i) for `t, y ≥ 0` and `T > 0`, `limsup_{x→∞} x⁻¹ log P_{xy}(T₁/x > T) ≤ ty + T log E e^{tU}`;
(ii) for `y ≥ 0` and `T > 0`,
`limsup_{x→∞} x⁻¹ log P_{xy}(∫_0^T (X_{⌊sx⌋}/x)^p ds ≥ 1) ≤ −𝒱^{T*}_y`. -/
theorem lemma_4_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    (∀ t y T : ℝ, 0 ≤ t → 0 ≤ y → 0 < T →
      limsup (fun x : ℝ => speedLog x
          (P {ω | ENNReal.ofReal (x * T) <
            ENat.toENNReal (retTime (fun k => lindley (x * y) U k ω) 1)})) atTop ≤
        ((t * y : ℝ) : EReal) + (T : EReal) * BellWilliams2001.ThresholdPolicy.logMGF P (U 0) t) ∧
    ∀ y T : ℝ, 0 ≤ y → 0 < T →
      limsup (fun x : ℝ => speedLog x
          (P {ω | 1 ≤ ∫⁻ s in Ioo 0 T,
            ENNReal.ofReal ((lindley (x * y) U ⌊s * x⌋₊ ω / x) ^ p)})) atTop ≤
        -((VTstar P U p T y : ℝ≥0∞) : EReal) := by sorry

end ReflectedRWLDP.SamplePath
