-- Prove2me | Theorems.Thm_RapidRatePoisson_WeakConv_theorem_1
-- name    : RapidRatePoisson.WeakConv.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:18:17.294283+00:00
-- url     : https://prove2.me/theorems/c6dde314-508f-4652-963c-b825a04f2473
-- title:
--   Theorem 1, p. 4 — under Assumption 1, N_ε ⇒ N_0 in D[0, ∞) as ε ↓ 0, N_0 Poisson with rate λ*
-- statement:
--   Let $N$ be a simple arrival counting process on a probability space $(\Omega,\mathcal F,P)$, adapted to a filtration $\mathcal F$, with $\mathcal F$-compensator $A$ (predictable, $A(0)=0$, non-decreasing right-continuous paths, $N-A$ an $\mathcal F$-martingale). Suppose Assumption 1 holds: $A(t)/t\to\lambda^*$ in probability as $t\to\infty$ for a deterministic $\lambda^*\in(0,\infty)$. For each $0<\varepsilon\le1$ let $\beta^\varepsilon=(\beta^\varepsilon_i)_{i\ge1}$ be iid Bernoulli($\varepsilon$), independent of $N$, and set
--   $$N_\varepsilon(t)=\sum_{i=1}^{N(t/\varepsilon)}\beta^\varepsilon_i,\qquad t\ge0 .$$
--
--   **Theorem 1.** As $\varepsilon\downarrow0$,
--   $$N_\varepsilon\Rightarrow N_0\quad\text{in }D[0,\infty),$$
--   where $D[0,\infty)$ carries the Skorokhod $J_1$ topology and $N_0=(N_0(t))_{t\ge0}$ is a Poisson process with constant intensity $\lambda^*$.
--
--   An arrival stream whose rate fluctuates on a fast time scale is thus approximated, in law on path space, by a homogeneous Poisson process with the long-run rate $\lambda^*$; queueing and service systems fed by such a stream can be analysed as if fed by Poisson arrivals.
--
--   **Formalization Note** "⇒ in $D[0,\infty)$" is the published coupling-form convergence in distribution `ConvInDist` with the $J_1$ topology on real càdlàg paths (equivalent to weak convergence of the laws on $D[0,\infty)$). "As $\varepsilon\downarrow0$" is stated along every sequence $\varepsilon_n\to0$ with $\varepsilon_n\in(0,1]$, which is equivalent because weak convergence of laws on $D[0,\infty)$ is metrizable. $N_0$ ranges over every Poisson process of rate $\lambda^*$ on any probability space (its law is unique). "Independent of $N$" is the independence of the mark sequence $(\beta^\varepsilon_1,\beta^\varepsilon_2,\dots)$ from the whole path of $N$, for each $\varepsilon$ separately; no joint independence across different $\varepsilon$ is assumed. The compensator is the predictable one (the page's paraphrase without predictability makes the theorem false; see the definitions file). Assumption 1's weak convergence to a constant is convergence in probability.
-- source:
--   Zheng, Honnappa & Glynn, arXiv:1807.06805v1, p. 4, Theorem 1 (with §2, p. 3, and Assumption 1, p. 4)

import Mathlib
import Definitions.Def_RapidRatePoisson_WeakConv_Model

namespace RapidRatePoisson.WeakConv
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

theorem theorem_1 {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 m) (N A : ℝ≥0 → Ω → ℝ) (lamStar : ℝ≥0)
    (hN : ∀ ω, MartingaleHT.InfiniteServer.IsUnitJumpCountingPath (fun t => N t ω))
    (hA : IsCompensator F P N A) (hA1 : Assumption1 P A lamStar)
    (β : ℝ≥0 → ℕ → Ω → Bool)
    (hβ : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 → IsBernoulliSeq P ε (β ε) ∧
      IndepFun (markSeq (β ε)) (fun ω (t : ℝ≥0) => N t ω) P)
    (εs : ℕ → ℝ≥0) (hεs : ∀ n, 0 < εs n ∧ εs n ≤ 1) (hεs0 : Tendsto εs atTop (𝓝 0))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (N0 : Ω' → ℝ → ℝ) (hN0 : RankBasedSDI.LoadBalancing.IsPoissonProcess P' lamStar N0) :
    PuhaWardFluid.Limit.ConvInDist (fun a b : ℝ => dist a b) P
      (fun n ω t => thinned N (β (εs n)) (εs n) t ω) P' (fun ω (t : ℝ≥0) => N0 ω t) := by sorry

end RapidRatePoisson.WeakConv
