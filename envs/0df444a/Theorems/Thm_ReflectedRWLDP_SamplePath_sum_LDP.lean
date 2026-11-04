-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_sum_LDP
-- name    : ReflectedRWLDP.SamplePath.sum_LDP
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-03T20:54:31.094706+00:00
-- url     : https://prove2.me/theorems/c9a5ecb7-2549-4234-acc7-1323a4dfb470
-- title:
--   Proof of Theorem 2.1, p. 17 — $\bar Z_n+\bar S_n$ satisfies the LDP in $(\mathbb D[0,1],\mathcal T_{M_1'})$ with rate $I_Y$ at speed $n^\alpha$
-- statement:
--   Let $U_1,U_2,\dots$ satisfy the standing assumptions of the paper (i.i.d., $\mathbf E U<0$, Assumptions 2.1–2.3, $p>0$), $\alpha=1/(1+p)$, and let $X$ be the reflected random walk started at $0$. Let
--   $$\bar Z_n(t)=\frac1n\sum_{j=1}^{N(nt)}W_j,\qquad \bar S_n(t)=\frac1n V_n\mathbf 1_{\{1\}}(t),\qquad t\in[0,1],$$
--   where $W_j$ is the area under $X^p$ during the $j$-th busy period, $N$ the renewal counting process of the returns to $0$, and $V_n$ the area under $X^p$ during the last (incomplete) busy period up to time $n$. Then $\bar Z_n+\bar S_n$ satisfies a large deviation principle in $(\mathbb D[0,1],\mathcal T_{M_1'})$ with speed $n^\alpha$ and rate function
--   $$I_Y(\zeta)=\begin{cases}\mathcal B^*_0\sum_{t:\zeta(t)\ne\zeta(t-)}(\zeta(t)-\zeta(t-))^\alpha&\text{if }\zeta\in\mathbb D^{(\lambda)}[0,1],\\ \infty&\text{otherwise,}\end{cases}$$
--   that is, for every $M_1'$-open $G$ and $M_1'$-closed $F$,
--   $$-\inf_{G}I_Y\le\liminf_{n\to\infty}\frac{\log\mathbf P(\bar Z_n+\bar S_n\in G)}{n^\alpha},\qquad\limsup_{n\to\infty}\frac{\log\mathbf P(\bar Z_n+\bar S_n\in F)}{n^\alpha}\le-\inf_F I_Y.$$
--
--   In the paper this is the first step of the proof of Theorem 2.1 (p. 17): the LDPs of $\bar Z_n$ (Lemma 3.7) and $\bar S_n$ (Lemma 3.1) are combined into an LDP for the pair, and the extended contraction principle is applied to the addition map, whose induced rate function equals $I_Y$. Theorem 2.1 then follows by the exponential equivalence of $\bar Y_n$ and $\bar Z_n+\bar S_n$ (Lemma 3.8).
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, p. 17, proof of Theorem 2.1, first paragraph ("we conclude that Z̄n + S̄n satisfies the sample-path LDP with the rate function I_Y")

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

/-- Step of the proof of **Theorem 2.1** (p. 17): from the LDPs of `Z̄_n` (Lemma 3.7) and `S̄_n`
(Lemma 3.1) and the extended contraction principle for `(ξ, ζ) ↦ ξ + ζ`, the sum `Z̄_n + S̄_n`
satisfies the LDP in `(𝔻[0,1], 𝒯_{M₁′})` with speed `n^α` and rate function `I_Y`. -/
theorem sum_LDP {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    SatisfiesLDP P (fun n ω => Zbar U p n ω + Sbar U p n ω) dM1 (fun n => (n : ℝ) ^ alpha p)
      (rateY P U p) := by sorry

end ReflectedRWLDP.SamplePath
