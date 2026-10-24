-- Prove2me | Theorems.Thm_PooledRationing_MaxWeighted_path_martingale_slln
-- name    : PooledRationing.MaxWeighted.path_martingale_slln
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-23T21:36:22.104514+00:00
-- url     : https://prove2.me/theorems/ba5621b1-5ed0-4384-a668-75ea71f18e7e
-- title:
--   Azuma + Borel–Cantelli: $T^{-a}\sum_{t<T}Z_{T,t}\to0$ a.s. for bounded path martingale differences, $a>1/2$
-- statement:
--   Let $(E,\mathcal E)$ be a measurable space with a probability measure $F$, and let $S\subseteq E$ be a measurable set with $F(S)=1$. Let $D^{(0)},D^{(1)},\dots$ be independent $E$-valued random variables on a probability space $(\Omega,\mu)$, each with law $F$, and write $\mathbf D(\omega)=(D^{(k)}(\omega))_{k\ge0}$ for the sample path.
--
--   For every horizon $T$ and index $t$ let $Z_{T,t}:E^{\mathbb N}\to\mathbb R$ be a measurable path functional such that:
--
--   1. **(adaptedness)** $Z_{T,t}(d)$ depends only on $d_0,\dots,d_t$;
--   2. **(bounded differences)** $|Z_{T,t}(d)|\le M$ for every path $d$ with all coordinates in $S$;
--   3. **(martingale difference)** for every path $d$ with all coordinates in $S$, $\int_E Z_{T,t}(d_0,\dots,d_{t-1},x,d_{t+1},\dots)\,F(dx)=0$.
--
--   Then for every $a>1/2$, almost surely
--   $$\lim_{T\to\infty}T^{-a}\sum_{t=0}^{T-1}Z_{T,t}(\mathbf D)=0 .$$
--
--   For each fixed $T$ the terms $Z_{T,t}(\mathbf D)$, $t=0,\dots,T-1$, form a bounded martingale-difference sequence for the filtration $\sigma(D^{(0)},\dots,D^{(t)})$. The array is triangular, though: the terms may depend on $T$. This strong law is the step in the proof of Theorem 3 where Azuma's inequality (Lemma 4) and the Borel–Cantelli lemma (Lemma 5) are combined. It disposes of the noise terms: with $a=\tfrac12+\epsilon$ for the terms $L_t$ of (55), and with $a=1$ for the service deviations used in the proof of (28).
-- source:
--   Jiang, Wang & Zhang, Achieving High Individual Service-Levels without Safety Stock? Optimal Rationing Policy of Pooled Resources, SSRN 3385089 (version of 31 July 2021), proof of Theorem 3, pp. 52-54 (the Azuma/Borel-Cantelli step used with Lemmas 4 and 5, p. 52-53)

import Mathlib
namespace PooledRationing.MaxWeighted

open MeasureTheory ProbabilityTheory Filter Topology

theorem path_martingale_slln
    {E : Type*} [MeasurableSpace E] (F : Measure E) [IsProbabilityMeasure F]
    (S : Set E) (hS : MeasurableSet S) (hFS : ∀ᵐ x ∂F, x ∈ S)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Dseq : ℕ → Ω → E) (hDmeas : ∀ t, Measurable (Dseq t))
    (hindep : iIndepFun Dseq μ) (hlaw : ∀ t, μ.map (Dseq t) = F)
    (Z : ℕ → ℕ → (ℕ → E) → ℝ) (hZmeas : ∀ T t, Measurable (Z T t))
    (hZloc : ∀ T t (d d' : ℕ → E), (∀ s ≤ t, d s = d' s) → Z T t d = Z T t d')
    (M : ℝ) (hZbdd : ∀ T t (d : ℕ → E), (∀ s, d s ∈ S) → |Z T t d| ≤ M)
    (hZcent : ∀ T t (d : ℕ → E), (∀ s, d s ∈ S) → ∫ x, Z T t (Function.update d t x) ∂F = 0)
    (a : ℝ) (ha : 1 / 2 < a) :
    ∀ᵐ ω ∂μ, Tendsto (fun T : ℕ => (T : ℝ) ^ (-a) *
      ∑ t ∈ Finset.range T, Z T t (fun k => Dseq k ω)) atTop (𝓝 0) := by sorry

end PooledRationing.MaxWeighted
