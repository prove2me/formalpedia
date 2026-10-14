-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_proposition_4_2
-- name    : ReflectedRWLDP.SamplePath.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:20.58545+00:00
-- url     : https://prove2.me/theorems/9ee9c512-1de8-4c25-8c7d-a14acc2aca22
-- title:
--   Proposition 4.2 — upper bound $-\mathcal B^*_y$ for the scaled busy-period area from $xy$, lower bound $-\mathcal B^*_0$ for $\mathbf P_0(W_1>u)$
-- statement:
--   Under the standing assumptions (i.i.d. increments with mean $\mu<0$, Assumptions 2.1–2.3, $p>0$), let $\alpha=1/(1+p)$.
--
--   1. For $y\ge0$, let $\mathbf P_{xy}$ be the law of the chain started at $X_0=xy$ and $T_1=\inf\{k>0:X_k=0\}$. Then
--   $$\limsup_{x\to\infty}\frac1x\log\mathbf P_{xy}\Big(\int_0^{T_1/x}(X_{\lfloor ux\rfloor}/x)^p\,du\ge1\Big)\le-\mathcal B^*_y .$$
--   2. For the chain started at $0$, with $W_1=\sum_{i=1}^{T_1}X_i^p$,
--   $$\liminf_{u\to\infty}\frac1{u^\alpha}\log\mathbf P_0(W_1>u)\ge-\mathcal B^*_0 .$$
--
--   Together with Proposition 4.3(i), these are the two halves of Theorem 2.2.
--
--   **Formalization Note** The hypothesis $y\ge0$ of part 1 is implicit in the paper; the chain lives on $[0,\infty)$. When $T_1=\infty$ the integral runs over $(0,\infty)$, and the region $u<T_1/x$ is written $ux<T_1$. Both limits are over the reals, in the extended reals with $\log0=-\infty$. $W_1\in[0,\infty]$.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, pp. 19–20, Proposition 4.2

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

/-- **Proposition 4.2** (pp. 19–20). (i) For `y ≥ 0`, with `X` started at `xy` and `T₁ = inf{k > 0 : X_k = 0}`,
`limsup_{x→∞} x⁻¹ log P_{xy}(∫_0^{T₁/x} (X_{⌊ux⌋}/x)^p du ≥ 1) ≤ −B*_y`.
(ii) `liminf_{u→∞} u^{−α} log P₀(W₁ > u) ≥ −B*₀`. -/
theorem proposition_4_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    (∀ y : ℝ, 0 ≤ y →
      limsup (fun x : ℝ => speedLog x
          (P {ω | 1 ≤ ∫⁻ u in {u : ℝ | 0 < u ∧ ENNReal.ofReal (u * x) <
              ENat.toENNReal (retTime (fun k => lindley (x * y) U k ω) 1)},
            ENNReal.ofReal ((lindley (x * y) U ⌊u * x⌋₊ ω / x) ^ p)})) atTop ≤
        -((Bstar P U p y : ℝ≥0∞) : EReal)) ∧
    -((Bstar P U p 0 : ℝ≥0∞) : EReal) ≤
      liminf (fun u : ℝ => speedLog (u ^ alpha p)
        (P {ω | ENNReal.ofReal u < W (chain U ω) p 1})) atTop := by sorry

end ReflectedRWLDP.SamplePath
