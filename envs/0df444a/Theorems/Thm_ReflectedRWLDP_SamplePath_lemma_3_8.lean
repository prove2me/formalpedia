-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_lemma_3_8
-- name    : ReflectedRWLDP.SamplePath.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:33.456811+00:00
-- url     : https://prove2.me/theorems/223437da-3f0f-4dcc-8a05-1652ba4000ee
-- title:
--   Lemma 3.8 — $\bar Y_n$ and $\bar Z_n+\bar S_n$ are exponentially equivalent in $(\mathbb D[0,1],\mathcal T_{M_1'})$
-- statement:
--   Under the standing assumptions (i.i.d. increments with mean $\mu<0$, Assumptions 2.1–2.3, $p>0$), let $\alpha=1/(1+p)$. The processes $\bar Y_n$ and $\bar Z_n+\bar S_n$ are exponentially equivalent in $(\mathbb D[0,1],\mathcal T_{M_1'})$ at speed $n^\alpha$: for every $\delta>0$,
--   $$\limsup_{n\to\infty}\frac1{n^\alpha}\log\mathbf P\big(d_{M_1'}(\bar Y_n,\bar Z_n+\bar S_n)>\delta\big)=-\infty .$$
--
--   Moving the last busy period's area to the end of the time horizon therefore does not change the large deviation behaviour of $\bar Y_n$.
--
--   **Formalization Note** Exponential equivalence follows Dembo–Zeitouni (Definition 4.2.10) with the metric $d_{M_1'}$, as used in the proof (p. 16). The sum $\bar Z_n+\bar S_n$ is the pointwise sum of the two paths.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, p. 16, Lemma 3.8

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

/-- **Lemma 3.8** (p. 16). `Ȳ_n` and `Z̄_n + S̄_n` are exponentially equivalent in `(𝔻[0,1], 𝒯_{M₁′})` at
speed `n^α`: for every `δ > 0`, `limsup_n n^{−α} log P(d_{M₁′}(Ȳ_n, Z̄_n + S̄_n) > δ) = −∞`. -/
theorem lemma_3_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    ExpEquivalent P (Ybar U p) (fun n ω => Zbar U p n ω + Sbar U p n ω) dM1
      (fun n => (n : ℝ) ^ alpha p) := by sorry

end ReflectedRWLDP.SamplePath
