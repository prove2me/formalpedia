-- Prove2me | Theorems.Thm_RapidRatePoisson_WeakConv_poisson_limit_dvj
-- name    : RapidRatePoisson.WeakConv.poisson_limit_dvj
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:18:19.151031+00:00
-- url     : https://prove2.me/theorems/a074122d-02ea-4ce0-9120-8192169f4568
-- title:
--   Theorem 13.4.IV of Daley and Vere-Jones (1988), cited in the proof of Theorem 1, p. 4 — compensators converging to λt give a Poisson limit
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and, for $n\ge0$, let $N_n$ be a simple counting process with a compensator $A_n$ with respect to a filtration $\mathcal G^{(n)}$ (each $n$ may have its own filtration): $A_n$ is $\mathcal G^{(n)}$-predictable, $A_n(0)=0$, its paths are non-decreasing and right-continuous, and $N_n-A_n$ is a $\mathcal G^{(n)}$-martingale. Let $\lambda\ge0$ and suppose that for every $t\ge0$,
--   $$A_n(t)\;\longrightarrow\;\lambda t\quad\text{in probability as }n\to\infty .$$
--   Then $N_n\Rightarrow N_0$ in $D[0,\infty)$ with the Skorokhod $J_1$ topology, where $N_0$ is a Poisson process with rate $\lambda$.
--
--   This is the general Poisson limit theorem for point processes driven by their compensators (Brown 1978; Daley and Vere-Jones 1988, Theorem 13.4.IV), in the form in which the proof of Theorem 1 applies it to $N_n=N_{\varepsilon_n}$ and $A_n=A_{\varepsilon_n}$.
--
--   **Formalization Note** The paper cites this result without printing it; the statement here is the one the proof of Theorem 1 applies, and it was not transcribed from the book. Convergence in distribution is the published coupling form `ConvInDist` (copies on a common probability space converging almost surely in $J_1$; equivalent to weak convergence of the laws on $D[0,\infty)$). The limit quantifies over every Poisson process of rate $\lambda$ on any probability space; the Poisson law on paths is unique. The compensators are predictable, which the theorem needs.
-- source:
--   Zheng, Honnappa & Glynn, arXiv:1807.06805v1, p. 4, proof of Theorem 1: "We now apply Theorem 13.4.IV of Daley and Vere-Jones (1988) to obtain the result." (Daley & Vere-Jones, An Introduction to the Theory of Point Processes, Springer 1988, Theorem 13.4.IV; statement chosen as applied, book not consulted)

import Mathlib
import Definitions.Def_RapidRatePoisson_WeakConv_Model

namespace RapidRatePoisson.WeakConv
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

theorem poisson_limit_dvj {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (G : ℕ → Filtration ℝ≥0 m) (Nn An : ℕ → ℝ≥0 → Ω → ℝ)
    (lam : ℝ≥0)
    (hN : ∀ n ω, MartingaleHT.InfiniteServer.IsUnitJumpCountingPath (fun t => Nn n t ω))
    (hA : ∀ n, IsCompensator (G n) P (Nn n) (An n))
    (hconv : ∀ t : ℝ≥0, TendstoInMeasure P (fun n => An n t) atTop (fun _ => (lam : ℝ) * t))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (N0 : Ω' → ℝ → ℝ) (hN0 : RankBasedSDI.LoadBalancing.IsPoissonProcess P' lam N0) :
    PuhaWardFluid.Limit.ConvInDist (fun a b : ℝ => dist a b) P
      (fun n ω t => Nn n t ω) P' (fun ω (t : ℝ≥0) => N0 ω t) := by sorry

end RapidRatePoisson.WeakConv
