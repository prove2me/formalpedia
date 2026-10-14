-- Prove2me | Theorems.Thm_ScheduledQueue_Diffusion_donsker_limit
-- name    : ScheduledQueue.Diffusion.donsker_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:01.981996+00:00
-- url     : https://prove2.me/theorems/5df66b41-feb8-4bfe-901d-ab65fe2f39fd
-- title:
--   Proof of Corollary 1, p. 5 — t^{-1/2} max_{s≤1} Σ_{i≤N(st)} (V_i − h) ⇒ √(Var V₁/h) X(1)
-- statement:
--   Under the standing assumptions (i.i.d. perturbations with $\mathbb E|\xi_0|<\infty$, $U$ uniform on $[0,1]$ independent of $\xi$, $h>0$), let $V_1,V_2,\dots$ be i.i.d. service times with finite variance, independent of $(U,\xi)$, with $\mathbb EV_1=h$. Let $B$ be a standard Brownian motion on some probability space and $X(1)=B(1)-\inf_{0\le u\le 1}B(u)$, the value at time $1$ of the reflected Brownian motion with mean $0$, unit volatility and $X(0)=0$. Then, as $t\to\infty$,
--   $$
--   t^{-1/2}\max_{0\le s\le 1}\sum_{i=1}^{N(st)}\big(V_i-h\big)\;\Rightarrow\;\sigma X(1),\qquad \sigma=\sqrt{\frac{\operatorname{Var}V_1}{h}} .
--   $$
--
--   This is the invariance-principle step of Corollary 1: the centered service-time random walk, run up to the random time $N(st)\approx st/h$, converges on the diffusion scale to a Brownian maximum, whose law is that of $\sigma X(1)$.
--
--   **Formalization Note** The page prints the limit as $\frac{\sigma}{\sqrt h}X(1)$ with $\sigma$ undefined in Corollary 1; with $\sigma^2=\operatorname{Var}V_1$ this equals $\sqrt{\operatorname{Var}V_1/h}\,X(1)$, which is the constant of (1.1) and is written explicitly here. $\operatorname{Var}V_1=0$ is allowed (the limit is then $0$). The Brownian motion is Mathlib's `IsBrownianReal` (indexed by $u\ge 0$, Gaussian finite-dimensional laws, almost surely continuous paths), on any probability space; the statement holds for every such $B$. Convergence in distribution (`TendstoInDistribution`) includes almost-everywhere measurability of every term and of the limit.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 5, proof of Corollary 1, display (second line); constant from (1.1), p. 2

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting

namespace ScheduledQueue.Diffusion

open MeasureTheory ProbabilityTheory Set Filter Topology NNReal

theorem donsker_limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U)
    (V : ℕ → Ω → ℝ) (hV : ServiceInput P ξ U V) (hmean : ∫ ω, V 1 ω ∂P = h)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsBrownianReal B P') :
    TendstoInDistribution
      (fun t : ℝ => fun ω => (Real.sqrt t)⁻¹ *
        ⨆ s : Icc (0 : ℝ) 1, ∑ i ∈ Finset.Icc 1 (ScheduledQueue.Stability.count h ξ U (s * t) ω), (V i ω - h))
      atTop (fun ω' => Real.sqrt (variance (V 1) P / h) * reflectedAtOne B ω') (fun _ => P) P' := by sorry

end ScheduledQueue.Diffusion
