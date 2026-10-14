-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_lemma_3_2
-- name    : ReflectedRWLDP.SamplePath.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:47.85039+00:00
-- url     : https://prove2.me/theorems/83be5584-922e-4b04-a8df-88eb01d574f2
-- title:
--   Lemma 3.2 — upper and lower bounds $-\mathcal B^*_0\sum_i(a_i-\lambda\Delta t_i)_+^\alpha$ for joint block-sum tails
-- statement:
--   Under the standing assumptions (i.i.d. increments with mean $\mu<0$, Assumptions 2.1–2.3, $p>0$), let $\alpha=1/(1+p)$. Let $W_j$ be the busy-period areas, $N(t)$ the renewal counting process and $\lambda$ the regenerative mean. Let $0=t_0<t_1<\dots<t_k$ with $k\ge1$, let $\Delta t_i=t_i-t_{i-1}$, and let $a_1,\dots,a_k$ be real numbers. Write
--   $$p_n=\mathbf P\Big(\sum_{j=1}^{N(nt_1)}W_j\ge na_1,\ \dots,\ \sum_{j=N(nt_{k-1})+1}^{N(nt_k)}W_j\ge na_k\Big).$$
--   Then
--   $$\limsup_{n\to\infty}\frac1{n^\alpha}\log p_n\le-\mathcal B^*_0\Big(\sum_{i=1}^k(a_i-\lambda\Delta t_i)_+^\alpha\Big),\qquad \liminf_{n\to\infty}\frac1{n^\alpha}\log p_n\ge-\mathcal B^*_0\Big(\sum_{i=1}^k(a_i-\lambda\Delta t_i)_+^\alpha\Big),$$
--   where $(x)_+=x\vee0$.
--
--   These bounds give the finite-dimensional large deviation principle of Lemma 3.3.
--
--   **Formalization Note** The $a_i$ are not quantified in the paper; the statement holds for every real vector $a$. The bound is trivial for $a_i\le0$. Block sums are computed in $[0,\infty]$ and compared with $na_i$ through `ENNReal.ofReal`, which is equivalent because the sums are nonnegative.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, p. 10, Lemma 3.2, (3.2)–(3.3)

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

/-- **Lemma 3.2** (p. 10). For `0 = t₀ < t₁ < ⋯ < t_k` (`k ≥ 1`) and reals `a₁, …, a_k`, the
probability that `∑_{j=N(nt_{i−1})+1}^{N(nt_i)} W_j ≥ n a_i` for all `i` decays at speed `n^α` with
exponent `−B*₀ ∑_{i=1}^k (a_i − λΔt_i)_+^α`: (3.2) bounds the `limsup` above and (3.3) the `liminf`
below. -/
theorem lemma_3_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) (k : ℕ) (hk : 0 < k) (t : Fin (k + 1) → ℝ) (ht0 : t 0 = 0)
    (ht : StrictMono t) (a : Fin k → ℝ) :
    limsup (fun n : ℕ => speedLog ((n : ℝ) ^ alpha p)
        (P {ω | ∀ i : Fin k, ENNReal.ofReal (n * a i) ≤
          ∑ j ∈ Finset.Ioc (Ncount (chain U ω) (n * t i.castSucc))
            (Ncount (chain U ω) (n * t i.succ)), W (chain U ω) p j})) atTop ≤
      -((Bstar P U p 0 * ∑ i : Fin k,
          ENNReal.ofReal ((max (a i - lam P U p * (t i.succ - t i.castSucc)) 0) ^ alpha p)
        : ℝ≥0∞) : EReal) ∧
    -((Bstar P U p 0 * ∑ i : Fin k,
          ENNReal.ofReal ((max (a i - lam P U p * (t i.succ - t i.castSucc)) 0) ^ alpha p)
        : ℝ≥0∞) : EReal) ≤
      liminf (fun n : ℕ => speedLog ((n : ℝ) ^ alpha p)
        (P {ω | ∀ i : Fin k, ENNReal.ofReal (n * a i) ≤
          ∑ j ∈ Finset.Ioc (Ncount (chain U ω) (n * t i.castSucc))
            (Ncount (chain U ω) (n * t i.succ)), W (chain U ω) p j})) atTop := by sorry

end ReflectedRWLDP.SamplePath
