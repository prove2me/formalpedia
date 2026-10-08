-- Prove2me | Theorems.Thm_SAARate_Polyhedral_lemma_2_4_b
-- name    : SAARate.Polyhedral.lemma_2_4_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:41.240699+00:00
-- url     : https://prove2.me/theorems/d4e1765e-97f5-421c-a2e0-784610b57f7f
-- title:
--   Lemma 2.4 (b), p. 6, (2.12) — w.p.1, sup_x ℋ(∂f̂_N(x), ∂f(x)) → 0
-- statement:
--   Let $\Omega$ be finite with probability measure $P$, let every $h(\cdot,\omega)$ be piecewise linear and convex on $\mathbb R^m$, and let $\omega^1,\omega^2,\dots$ be an i.i.d. sample from $P$. With $f$, $\hat f_N$ and $\partial$ as in the mission's setting and $\mathcal H$ the Hausdorff distance between subsets of $\mathbb R^m$, with probability one
--   $$
--   \lim_{N\to\infty}\ \sup_{x\in\mathbb R^m}\ \mathcal H\big(\partial\hat f_N(x),\,\partial f(x)\big)=0 .
--   $$
--
--   The subdifferentials of the sample average function converge to those of the true expected value function uniformly over the whole space. This is the route to Theorem 2.3 through optimality conditions.
--
--   **Formalization Note** The Hausdorff distance is Mathlib's extended Hausdorff distance (values in $[0,\infty]$), and the supremum is taken in $[0,\infty]$. The statement concerns one i.i.d. sequence: "w.p.1" means for almost every sample path.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 6, Lemma 2.4 (b), (2.12)

import Mathlib
import Definitions.Def_SAARate_Polyhedral_Setting
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential

open MeasureTheory ProbabilityTheory Filter Topology ShorNonsmooth.Subdiff

namespace SAARate.Polyhedral

/-- Lemma 2.4 (b), p. 6, (2.12): under (i) and (ii), with probability one the subdifferentials
`∂f̂_N(x)` converge to `∂f(x)` uniformly in `x ∈ ℝ^m`, in the Hausdorff distance. -/
theorem lemma_2_4_b {m : ℕ} {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : SAARate.Sharp.E m → Ω → ℝ) (hpl : ∀ ω, IsPLConvex (fun x => h x ω))
    {S : Type*} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (ω : ℕ → S → Ω) (hω : SAARate.SharpLD.IsIIDSample Q P ω) :
    ∀ᵐ s ∂Q, Tendsto (fun N : ℕ => ⨆ x : SAARate.Sharp.E m,
        Metric.hausdorffEDist (subdifferential Set.univ (SAARate.Sharp.saaObj h (fun j => ω j s) N) x)
          (subdifferential Set.univ (SAARate.Sharp.expectedObj P h) x)) atTop (𝓝 0) := by sorry

end SAARate.Polyhedral
