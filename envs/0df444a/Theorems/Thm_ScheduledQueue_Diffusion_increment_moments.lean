-- Prove2me | Theorems.Thm_ScheduledQueue_Diffusion_increment_moments
-- name    : ScheduledQueue.Diffusion.increment_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:54.422281+00:00
-- url     : https://prove2.me/theorems/f08f30e5-0113-4431-aa8a-ff0e57abab35
-- title:
--   Proof of Proposition 1, p. 4 — N((k+1)h) − N(kh) identically distributed, E exp(θN(h)) < ∞
-- statement:
--   Under the standing assumptions (i.i.d. perturbations with $\mathbb E|\xi_0|<\infty$, $U$ uniform on $[0,1]$ independent of $\xi$, $h>0$), write $N(a,b]$ for the number of arrivals in $(a,b]$. Then
--
--   1. the increments $N(kh,(k+1)h]$, $k=0,1,2,\dots$, are identically distributed, all with the law of $N(0,h]=N(h)$;
--   2. for every $\theta>0$, $N(h)<\infty$ almost surely and
--   $$
--   \mathbb E\exp\big(\theta N(h)\big)<\infty .
--   $$
--
--   These two facts let the maximal argument for $\mathcal E$ be repeated for the increments of $N$ over the slots $[kh,(k+1)h]$ in the proof of Proposition 1.
--
--   **Formalization Note** The page cites both facts from Araman et al. (2022). The increments are extended natural numbers; the expectation is a lower Lebesgue integral, and its finiteness is the claim.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 4, proof of Proposition 1, last paragraph

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting

namespace ScheduledQueue.Diffusion

open MeasureTheory ProbabilityTheory Set Filter Topology NNReal

theorem increment_moments {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) :
    (∀ k : ℕ, IdentDistrib (arrivalsIn h ξ U ((k : ℝ) * h) (((k : ℝ) + 1) * h))
        (arrivalsIn h ξ U 0 h) P P) ∧
    ∀ θ : ℝ, 0 < θ →
      (∀ᵐ ω ∂P, arrivalsIn h ξ U 0 h ω ≠ ⊤) ∧
      ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * ((arrivalsIn h ξ U 0 h ω).toNat : ℝ))) ∂P < ⊤ := by sorry

end ScheduledQueue.Diffusion
