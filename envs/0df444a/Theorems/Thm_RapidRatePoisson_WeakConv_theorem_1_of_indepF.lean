-- Prove2me | Theorems.Thm_RapidRatePoisson_WeakConv_theorem_1_of_indepF
-- name    : RapidRatePoisson.WeakConv.theorem_1_of_indepF
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-31T11:15:39.222146+00:00
-- url     : https://prove2.me/theorems/aef4e0e6-043f-4d83-9ef2-8313ac2d2771
-- title:
--   Theorem 1, p. 4 — N_ε ⇒ Poisson(λ*) in D[0,∞), with marks independent of F_∞ and E N(t) < ∞
-- statement:
--   Let $N$ be a simple arrival counting process on a probability space $(\Omega,\mathcal F,P)$ with predictable $\mathcal F$-compensator $A$ (predictable, $A(0)=0$, non-decreasing right-continuous paths, $N-A$ an $\mathcal F$-martingale), with $E\,N(t)<\infty$ for all $t$, and suppose Assumption 1 holds: $A(t)/t\to\lambda^*$ in probability as $t\to\infty$ for a deterministic $\lambda^*\in(0,\infty)$. For each $0<\varepsilon\le1$ let $\beta^\varepsilon=(\beta^\varepsilon_i)_{i\ge1}$ be iid Bernoulli($\varepsilon$), with the sequence $\beta^\varepsilon$ independent of $\mathcal F_\infty=\bigvee_t\mathcal F_t$, and set
--   $$N_\varepsilon(t)=\sum_{i=1}^{N(t/\varepsilon)}\beta^\varepsilon_i,\qquad t\ge0 .$$
--   Then, as $\varepsilon\downarrow0$,
--   $$N_\varepsilon\Rightarrow N_0\quad\text{in }D[0,\infty)$$
--   with the Skorokhod $J_1$ topology, where $N_0$ is a Poisson process with constant intensity $\lambda^*$.
--
--   This is Theorem 1 of the paper under exactly the hypotheses its proof uses: the proof identifies $A_\varepsilon(t)=\varepsilon A(t/\varepsilon)$ as the compensator of $N_\varepsilon$ for the filtration $\mathcal G^\varepsilon_t=\mathcal F_{t/\varepsilon}\vee\sigma(\beta^\varepsilon_i:i\le N(t/\varepsilon))$, which needs the marks to be independent of $\mathcal F_\infty$ (not only of $N$) and needs $N_\varepsilon(t)$ to be integrable; it then shows $A_\varepsilon(t)\to\lambda^*t$ in probability and applies the Poisson limit theorem of Daley and Vere-Jones (Theorem 13.4.IV).
--
--   **Formalization Note** Same conventions as the mission's goal `RapidRatePoisson.WeakConv.theorem_1` (coupling-form `ConvInDist` with the $J_1$ topology, $\varepsilon\downarrow0$ along every sequence $\varepsilon_n\to0$ in $(0,1]$, $N_0$ any rate-$\lambda^*$ Poisson process). Compared with the goal, the hypothesis "$\beta^\varepsilon$ independent of the path of $N$" is replaced by "the $\sigma$-algebra of $(\beta^\varepsilon_1,\beta^\varepsilon_2,\dots)$ is independent of $\bigvee_t\mathcal F_t$" (which implies it, since $N$ is adapted), and $E\,N(t)<\infty$ is added; these are the two hypotheses added in the milestone `thinned_compensator`.
-- source:
--   Zheng, Honnappa & Glynn, arXiv:1807.06805v1, p. 4, Theorem 1 and its proof (with §2, p. 3, and Assumption 1, p. 4)

import Mathlib
import Definitions.Def_RapidRatePoisson_WeakConv_Model

namespace RapidRatePoisson.WeakConv
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

theorem theorem_1_of_indepF {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 m) (N A : ℝ≥0 → Ω → ℝ) (lamStar : ℝ≥0)
    (hN : ∀ ω, MartingaleHT.InfiniteServer.IsUnitJumpCountingPath (fun t => N t ω))
    (hA : IsCompensator F P N A) (hA1 : Assumption1 P A lamStar)
    (hNint : ∀ t, Integrable (N t) P)
    (β : ℝ≥0 → ℕ → Ω → Bool)
    (hβ : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 → IsBernoulliSeq P ε (β ε) ∧
      Indep (MeasurableSpace.comap (markSeq (β ε)) inferInstance) (⨆ t, F t) P)
    (εs : ℕ → ℝ≥0) (hεs : ∀ n, 0 < εs n ∧ εs n ≤ 1) (hεs0 : Tendsto εs atTop (𝓝 0))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (N0 : Ω' → ℝ → ℝ) (hN0 : RankBasedSDI.LoadBalancing.IsPoissonProcess P' lamStar N0) :
    PuhaWardFluid.Limit.ConvInDist (fun a b : ℝ => dist a b) P
      (fun n ω t => thinned N (β (εs n)) (εs n) t ω) P' (fun ω (t : ℝ≥0) => N0 ω t) := by sorry

end RapidRatePoisson.WeakConv
