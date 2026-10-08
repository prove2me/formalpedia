-- Prove2me | Theorems.Thm_ReedGGN_SystemEq_prop_2_1_arrival_delay
-- name    : ReedGGN.SystemEq.prop_2_1_arrival_delay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:41.981278+00:00
-- url     : https://prove2.me/theorems/3088f9a0-4c48-4771-8656-4cad7175e7db
-- title:
--   Proof of Proposition 2.1, first two equalities (p. 8) — G(t − τᵢ − wᵢ) − G(t − τᵢ) is the F-mass of the delay window
-- statement:
--   Let $F$ be a service-time distribution on $[0,\infty)$, with tail $G=1-F$, and fix a sample path of the $G/GI/N$ queue with arrival times $\tau_i$, nonnegative waiting times $w_i$ and arrival counting process $A$. Then for every $t\ge 0$,
--   $$\sum_{i=1}^{A(t)}\big(G(t-\tau_i-w_i)-G(t-\tau_i)\big)=\sum_{i=1}^{A(t)}\int_0^\infty 1\{t-(\tau_i+w_i)<s\le t-\tau_i\}\,dF(s).$$
--
--   Each difference of tails is the probability that a service time falls in the window $(t-\tau_i-w_i,\,t-\tau_i]$ of length $w_i$; this is the first step of the proof of Proposition 2.1, which then turns the window into the event "customer $i$ is waiting at time $t-s$".
--
--   **Formalization Note** The paper's intermediate form $\int_{(t-(\tau_i+w_i))^+}^{t-\tau_i}dF(s)$ is ambiguous when $F$ has an atom at $0$; the statement uses the paper's next form, with the half-open window, which fixes the convention. $\int_0^\infty$ is the integral over $[0,\infty)$, the point $0$ included. $F$ is a probability measure $\mu$ on $\mathbb R$ with $\mu((-\infty,0))=0$ and $G(x)=\mu((x,\infty))$ for every real $x$.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 8, proof of Proposition 2.1, first and second equalities of the chain

import Mathlib
import Definitions.Def_ReedGGN_SystemEq_QueueLength

namespace ReedGGN.SystemEq

open MeasureTheory

/-- Proof of Proposition 2.1, first two equalities (p. 8): for each arrival `i ≤ A(t)`, the
difference `G(t − τ_i − w_i) − G(t − τ_i)` is the `F`-mass of the delay window
`{s ≥ 0 : t − (τ_i + w_i) < s ≤ t − τ_i}`, so
`Σ_{i=1}^{A(t)} (G(t − τ_i − w_i) − G(t − τ_i))
  = Σ_{i=1}^{A(t)} ∫_0^∞ 1{t − (τ_i + w_i) < s ≤ t − τ_i} dF(s)`. -/
theorem prop_2_1_arrival_delay (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (P : SamplePath) (t : ℝ) (ht : 0 ≤ t) :
    ∑ i ∈ Finset.Icc 1 (P.A t), (G μ (t - P.τ i - P.w i) - G μ (t - P.τ i)) =
      ∑ i ∈ Finset.Icc 1 (P.A t),
        ∫ s in Set.Ici 0, (Set.Ioc (t - (P.τ i + P.w i)) (t - P.τ i)).indicator
          (fun _ => (1 : ℝ)) s ∂μ := by sorry

end ReedGGN.SystemEq
