-- Prove2me | Theorems.Thm_ScheduledQueue_Diffusion_maximal_bounds
-- name    : ScheduledQueue.Diffusion.maximal_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:17.064056+00:00
-- url     : https://prove2.me/theorems/44fc734e-9b94-4d07-9dd1-4bedc626f5ed
-- title:
--   Proof of Proposition 1, p. 4 — (1/log n) max_k 𝓔(kh), max_k 𝓛(kh), max_k (N((k+1)h) − N(kh)) →p 0
-- statement:
--   Under the standing assumptions (i.i.d. perturbations with $\mathbb E|\xi_0|<\infty$, $U$ uniform on $[0,1]$ independent of $\xi$, $h>0$), as $n\to\infty$,
--   $$
--   \frac{1}{\log n}\max_{1\le k\le n+1}\mathcal E(kh)\xrightarrow{p}0,\qquad
--   \frac{1}{\log n}\max_{0\le k\le n}\mathcal L(kh)\xrightarrow{p}0,\qquad
--   \frac{1}{\log n}\max_{0\le k\le n+1}\big(N((k+1)h)-N(kh)\big)\xrightarrow{p}0 .
--   $$
--
--   These three maximal bounds, combined with the decomposition of $N$, give Proposition 1.
--
--   **Formalization Note** Convergence in probability is Lean's `TendstoInMeasure`. The counts are extended natural numbers converted by `toNat`, which is $0$ at $\infty$; they are almost surely finite (by the exponential moment bounds), so this affects only a null event. The increment $N((k+1)h)-N(kh)$ is the number of arrivals in $(kh,(k+1)h]$. For $n\le 1$, $1/\log n$ is a junk value, irrelevant to the limit.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 4, proof of Proposition 1, last paragraph

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting

namespace ScheduledQueue.Diffusion

open MeasureTheory ProbabilityTheory Set Filter Topology NNReal

theorem maximal_bounds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) :
    TendstoInMeasure P
        (fun (n : ℕ) ω => (Real.log n)⁻¹ *
          (((Finset.Icc 1 (n + 1)).sup fun k => (early h ξ U ((k : ℝ) * h) ω).toNat : ℕ) : ℝ))
        atTop (fun _ => 0) ∧
    TendstoInMeasure P
        (fun (n : ℕ) ω => (Real.log n)⁻¹ *
          (((Finset.range (n + 1)).sup fun k => (late h ξ U ((k : ℝ) * h) ω).toNat : ℕ) : ℝ))
        atTop (fun _ => 0) ∧
    TendstoInMeasure P
        (fun (n : ℕ) ω => (Real.log n)⁻¹ *
          (((Finset.range (n + 2)).sup fun k =>
              (arrivalsIn h ξ U ((k : ℝ) * h) (((k : ℝ) + 1) * h) ω).toNat : ℕ) : ℝ))
        atTop (fun _ => 0) := by sorry

end ScheduledQueue.Diffusion
