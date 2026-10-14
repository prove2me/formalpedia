-- Prove2me | Theorems.Thm_ScheduledQueue_Diffusion_corollary_1
-- name    : ScheduledQueue.Diffusion.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:12.280062+00:00
-- url     : https://prove2.me/theorems/f0c142a1-2526-41c3-9e7b-c05f1618654c
-- title:
--   Corollary 1 — at critical loading, t^{-1/2} W(t) ⇒ σX(1) with σ² = Var V₁/h and X reflected Brownian motion
-- statement:
--   Consider a single-server queue with unit service rate, empty at time $0$, fed by scheduled traffic: customer $j\in\mathbb Z$ is scheduled at time $jh$ ($h>0$) and arrives at $jh+hU+\xi_j$, where the perturbations $\xi_j$ are i.i.d. with $\mathbb E|\xi_0|<\infty$ and $U$ is uniform on $[0,1]$ and independent of $\xi$. Let $N(t)$ be the number of arrivals in $(0,t]$, and let the service times $V_1,V_2,\dots$ be i.i.d., independent of $(U,\xi)$, with $\operatorname{Var}V_1<\infty$. The workload at time $t\ge 0$ is
--   $$
--   W(t)=\sup_{0\le s\le t}\Big(\sum_{i=N(s)+1}^{N(t)}V_i-(t-s)\Big).
--   $$
--   If $h=\mathbb EV_1$ (critical loading), then, as $t\to\infty$,
--   $$
--   t^{-1/2}\,W(t)\;\Rightarrow\;\sigma X(1),\qquad \sigma^2=\frac{\operatorname{Var}V_1}{h},
--   $$
--   where $X=(X(s):s\ge 0)$ is a reflected Brownian motion with mean $0$ and unit volatility, with $X(0)=0$; concretely $X(1)=B(1)-\inf_{0\le u\le 1}B(u)$ for a standard Brownian motion $B$.
--
--   The limit is the same as for a queue fed by a deterministic arrival stream with the same service times: the perturbations, however heavy-tailed (as long as they have a finite mean), do not affect the diffusion-scale workload. In particular, if $\operatorname{Var}V_1>0$, then $W(t)\Rightarrow\infty$ and the critically loaded queue is unstable.
--
--   **Formalization Note** $\sigma^2=\operatorname{Var}V_1/h$ is taken from (1.1) on p. 2, since Corollary 1 does not define $\sigma$; $\operatorname{Var}V_1=0$ is allowed and then the limit is the point mass at $0$. The page's workload formula has the index range $N(s),\dots,N(t)$, which gives $W(0)\ne 0$; the range $N(s)+1,\dots,N(t)$ used here is the one consistent with an empty system at time $0$. The statement quantifies over every standard Brownian motion $B$ (Mathlib's `IsBrownianReal`) on every probability space; the law of the limit does not depend on this choice. Convergence in distribution (`TendstoInDistribution`) includes almost-everywhere measurability of every $t^{-1/2}W(t)$ and of the limit. The factor $(\sqrt t)^{-1}$ is a junk value for $t\le 0$, irrelevant to the limit as $t\to\infty$.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 4, Corollary 1; σ from (1.1), p. 2

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting

namespace ScheduledQueue.Diffusion

open MeasureTheory ProbabilityTheory Set Filter Topology NNReal

theorem corollary_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U)
    (V : ℕ → Ω → ℝ) (hV : ServiceInput P ξ U V) (hmean : ∫ ω, V 1 ω ∂P = h)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsBrownianReal B P') :
    TendstoInDistribution (fun t : ℝ => fun ω => (Real.sqrt t)⁻¹ * workload h ξ U V t ω) atTop
      (fun ω' => Real.sqrt (variance (V 1) P / h) * reflectedAtOne B ω') (fun _ => P) P' := by sorry

end ScheduledQueue.Diffusion
