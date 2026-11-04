-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_lemma_4_6_ii
-- name    : ReflectedRWLDP.SamplePath.lemma_4_6_ii
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-03T20:47:10.478116+00:00
-- url     : https://prove2.me/theorems/168a3656-bcfa-4177-85fb-abb7a66b7b94
-- title:
--   Lemma 4.6 (ii), p. 23 — $\limsup_{x\to\infty}\frac1x\log P_{xy}\big(\int_0^T(X_{\lfloor sx\rfloor}/x)^p ds\ge1\big)\le-\mathcal V^{T*}_y$ (4.6)
-- statement:
--   Let $U_1,U_2,\dots$ satisfy the standing assumptions of the paper (i.i.d., $\mathbf E U<0$, Assumptions 2.1–2.3, $p>0$), and let $X$ be the reflected random walk $X_{k+1}=[X_k+U_{k+1}]^+$ started at $X_0=xy$, with law $\mathbf P_{xy}$. Then for any $y\ge0$ and $T>0$,
--   $$\limsup_{x\to\infty}\frac1x\log\mathbf P_{xy}\Big(\int_0^T\big(X_{\lfloor sx\rfloor}/x\big)^p\,ds\ge1\Big)\le-\mathcal V^{T*}_y, \tag{4.6}$$
--   where $\mathcal V^{T*}_y=\inf\{I^{\mathbb{BV}[0,T]}_y(\xi):\xi\in\mathbb D[0,T],\ \xi(0)=y,\ \Phi_T(\xi)\ge1\}$ is the value of the finite-horizon variational problem $(\mathcal V^T_y)$ and $\Phi_T(\xi)=\int_0^T\Psi(\xi)(s)^p\,ds$.
--
--   This is part (ii) of Lemma 4.6; part (i), the bound (4.5), is `ReflectedRWLDP.SamplePath.lemma_4_6_i`. The paper derives it from the sample-path LDP for the scaled random walk in the $M_1'$ topology together with the uniform continuity of $\Phi_T$ on level sets (Lemma 4.5).
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, p. 23, Lemma 4.6 (ii), (4.6); proof p. 23

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

/-- **Lemma 4.6 (ii)** (p. 23), bound (4.6). For the reflected random walk started at `xy`,
`limsup_{x→∞} x⁻¹ log P_{xy}(∫_0^T (X_{⌊sx⌋}/x)^p ds ≥ 1) ≤ −𝒱^{T*}_y` for all `y ≥ 0`, `T > 0`. -/
theorem lemma_4_6_ii {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    ∀ y T : ℝ, 0 ≤ y → 0 < T →
      limsup (fun x : ℝ => speedLog x
          (P {ω | 1 ≤ ∫⁻ s in Ioo 0 T,
            ENNReal.ofReal ((lindley (x * y) U ⌊s * x⌋₊ ω / x) ^ p)})) atTop ≤
        -((VTstar P U p T y : ℝ≥0∞) : EReal) := by sorry

end ReflectedRWLDP.SamplePath
