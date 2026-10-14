-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_theorem_2_3
-- name    : ReflectedRWLDP.SamplePath.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:28.491881+00:00
-- url     : https://prove2.me/theorems/a8519fa9-b550-434a-945f-53ed8c1e86b6
-- title:
--   Theorem 2.3 — $\lim_{n\to\infty}n^{-\alpha}\log\mathbf P(V_n\ge nb)=-\mathcal B^*_0b^\alpha$ for the last busy period
-- statement:
--   Under the standing assumptions (i.i.d. increments with mean $\mu<0$, Assumptions 2.1–2.3, $p>0$), let $X$ be the reflected random walk started at $0$, $\alpha=1/(1+p)$, and let
--   $$V_n=\sum_{i=T_{N(n)}+1}^{n}X_i^p$$
--   be the area under $X^p$ during the last busy period up to time $n$, where $N(n)=\max\{k:T_k\le n\}$. For every $b\ge0$,
--   $$\lim_{n\to\infty}\frac1{n^\alpha}\log\mathbf P(V_n\ge nb)=-\mathcal B^*_0\cdot b^\alpha .$$
--
--   The busy period in progress at time $n$ has the same tail as a complete busy period. This gives the large deviation principle for $\bar S_n$ (Lemma 3.1).
--
--   **Formalization Note** $n\to\infty$ over the naturals; the limit is in the extended reals.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, p. 8, Theorem 2.3, (2.5)

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

/-- **Theorem 2.3** (p. 8). For every `b ≥ 0`, the area `V_n = ∑_{i=T_{N(n)}+1}^n X_i^p` of the last
busy period satisfies `lim_{n→∞} n^{−α} log P(V_n ≥ nb) = −B*₀ · b^α`. -/
theorem theorem_2_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) (b : ℝ) (hb : 0 ≤ b) :
    Tendsto (fun n : ℕ => speedLog ((n : ℝ) ^ alpha p)
        (P {ω | (n : ℝ) * b ≤ V (chain U ω) p n}))
      atTop (𝓝 (-((Bstar P U p 0 * ENNReal.ofReal (b ^ alpha p) : ℝ≥0∞) : EReal))) := by sorry

end ReflectedRWLDP.SamplePath
