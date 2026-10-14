-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_lemma_3_1
-- name    : ReflectedRWLDP.SamplePath.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:38.32303+00:00
-- url     : https://prove2.me/theorems/35f1a163-a05d-4358-b984-f2de3ee23b70
-- title:
--   Lemma 3.1 — LDP for $\bar S_n=\frac1nV_n\mathbb 1_{\{1\}}$ in $(\mathbb D[0,1],\mathcal T_{M_1'})$ with rate $I_S$
-- statement:
--   Under the standing assumptions (i.i.d. increments with mean $\mu<0$, Assumptions 2.1–2.3, $p>0$), let $\alpha=1/(1+p)$ and $\bar S_n=\frac1nV_n\mathbb 1_{\{1\}}$. Then $\bar S_n$ satisfies the large deviation principle in $(\mathbb D[0,1],\mathcal T_{M_1'})$ with speed $n^\alpha$ and rate function
--   $$I_S(\zeta)=\begin{cases}\mathcal B^*_0(\zeta(1)-\zeta(1-))^\alpha&\text{if }\zeta\in\mathbb D[0,1]^{\leqslant1},\\ \infty&\text{otherwise,}\end{cases}$$
--   where $\mathbb D[0,1]^{\leqslant1}=\{\xi\in\mathbb D[0,1]:\xi=x\mathbb 1_{\{1\}}\text{ for some }x\ge0\}$.
--
--   This is the large deviation principle for the contribution of the last, incomplete busy period.
--
--   **Formalization Note** The statement does not assert that $I_S$ is a good rate function, and neither does the formalization.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, p. 9, Lemma 3.1, (3.1)

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

/-- **Lemma 3.1** (p. 9). `S̄_n = (1/n) V_n 𝟙_{{1}}` satisfies the LDP in `(𝔻[0,1], 𝒯_{M₁′})` with speed
`n^α` and rate function `I_S(ζ) = B*₀ (ζ(1) − ζ(1−))^α` on `𝔻[0,1]^{⩽1}`, `∞` elsewhere. -/
theorem lemma_3_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    SatisfiesLDP P (Sbar U p) dM1 (fun n => (n : ℝ) ^ alpha p) (rateS P U p) := by sorry

end ReflectedRWLDP.SamplePath
