-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_lemma_3_7
-- name    : ReflectedRWLDP.SamplePath.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:29.53753+00:00
-- url     : https://prove2.me/theorems/a3406179-3edc-412c-bdcd-e5102448afa5
-- title:
--   Lemma 3.7 — LDP for $\bar Z_n$ in $(\mathbb D[0,1],\mathcal T_{M_1'})$ with the good rate function $I_Z$
-- statement:
--   Under the standing assumptions (i.i.d. increments with mean $\mu<0$, Assumptions 2.1–2.3, $p>0$), let $\alpha=1/(1+p)$ and $\bar Z_n(t)=\frac1n\sum_{j=1}^{N(nt)}W_j$, $t\in[0,1]$. Then $\bar Z_n$ satisfies the large deviation principle in $\mathbb D[0,1]$ with respect to the $M_1'$ topology, with speed $n^\alpha$ and the good rate function
--   $$I_Z(\xi)=\begin{cases}\mathcal B^*_0\sum_{t:\xi(t)\ne\xi(t-)}(\xi(t)-\xi(t-))^\alpha&\text{if }\xi\in\mathbb D^{(\lambda)}[0,1],\\ \infty&\text{otherwise.}\end{cases}$$
--
--   This is the sample-path large deviation principle for the completed busy periods.
--
--   **Formalization Note** $I_Z$ in (3.13) is the same function as $I_Y$ in (2.1) with $T=1$, and the formalization defines it once (`rateY`). Jumps use $\xi(0-)=0$.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, p. 15, Lemma 3.7 (I_Z as in (3.13), p. 14)

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

/-- **Lemma 3.7** (p. 15). `Z̄_n(t) = (1/n) ∑_{j=1}^{N(nt)} W_j` satisfies the LDP in `𝔻[0,1]` w.r.t. the
`M₁′` topology with speed `n^α` and the good rate function `I_Z` of (3.13), which is the function `I_Y`
of (2.1) with `T = 1` (`rateY`). -/
theorem lemma_3_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    SatisfiesLDP P (Zbar U p) dM1 (fun n => (n : ℝ) ^ alpha p) (rateY P U p) ∧
      MFGLimit.LDP.IsGoodRate dM1 (rateY P U p) := by sorry

end ReflectedRWLDP.SamplePath
