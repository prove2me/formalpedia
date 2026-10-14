-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_theorem_2_2
-- name    : ReflectedRWLDP.SamplePath.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:16.670985+00:00
-- url     : https://prove2.me/theorems/bc92fe3f-3fc7-4254-b63c-baed1e5dadca
-- title:
--   Theorem 2.2 — $\lim_{t\to\infty}t^{-\alpha}\log\mathbf P(W_1\ge t)=-\mathcal B^*_0$
-- statement:
--   Let $X_{n+1}=[X_n+U_{n+1}]^+$, $X_0=0$, be the reflected random walk under the standing assumptions (i.i.d. increments with mean $\mu<0$, Assumptions 2.1–2.3, $p>0$), and let $\alpha=1/(1+p)$. Let $T_1$ be the first return time to $0$ and
--   $$W_1=\sum_{k=1}^{T_1}X_k^p$$
--   the area under $X^p$ during the first busy period. Then
--   $$\lim_{t\to\infty}\frac1{t^\alpha}\log\mathbf P(W_1\ge t)=-\mathcal B^*_0 .$$
--
--   The tail of the busy-period area is of Weibull type with exponent $\alpha$, and its constant is the value of the variational problem $(\mathcal B_0)$.
--
--   **Formalization Note** $t\to\infty$ over the reals. The limit is in the extended reals with $\log0=-\infty$, and $W_1\in[0,\infty]$.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, p. 8, Theorem 2.2, (2.4)

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

/-- **Theorem 2.2** (p. 8). For the chain started at `0`, with `W₁ = ∑_{k=1}^{T₁} X_k^p`,
`lim_{t→∞} t^{−α} log P(W₁ ≥ t) = −B*₀`. -/
theorem theorem_2_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    Tendsto (fun t : ℝ => speedLog (t ^ alpha p) (P {ω | ENNReal.ofReal t ≤ W (chain U ω) p 1}))
      atTop (𝓝 (-((Bstar P U p 0 : ℝ≥0∞) : EReal))) := by sorry

end ReflectedRWLDP.SamplePath
