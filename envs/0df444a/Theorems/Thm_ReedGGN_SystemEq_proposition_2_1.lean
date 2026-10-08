-- Prove2me | Theorems.Thm_ReedGGN_SystemEq_proposition_2_1
-- name    : ReedGGN.SystemEq.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:47.722736+00:00
-- url     : https://prove2.me/theorems/d7e25b2f-3726-4bf4-9145-ec65a452f58b
-- title:
--   Proposition 2.1 (p. 8) — Σ_{i≤A(t)} (G(t − τᵢ − wᵢ) − G(t − τᵢ)) = ∫₀ᵗ (Q(t − s) − N)⁺ dF(s) − Σ (G(t − w̃ᵢ) − G(t))
-- statement:
--   Let $F$ be a service-time distribution on $[0,\infty)$ with tail $G=1-F$, and fix a non-idling sample path of the $G/GI/N$ queue: $N$ servers, $Q_0$ initial customers, arrival times $\tau_i$ with counting process $A$, waiting times $w_i$ of the arrivals and $\tilde w_i$ of the initial customers $N+i$, and number in system $Q(t)$ given by (2.2). Then for each $t\ge 0$,
--   $$\sum_{i=1}^{A(t)}\big(G(t-\tau_i-w_i)-G(t-\tau_i)\big)=\int_0^t (Q(t-s)-N)^+\,dF(s)-\sum_{i=1}^{(Q_0-N)^+}\big(G(t-\tilde w_i)-G(t)\big).$$
--
--   The left side is the correction that the waiting times make to the infinite-server terms in (2.7). The proposition expresses it through the number of waiting customers $(Q-N)^+$ alone, which is what turns (2.7) into the closed system equation (2.8).
--
--   **Formalization Note** "Non-idling" is the identity $(Q(t)-N)^+=\sum_{i\le (Q_0-N)^+}1\{t<\tilde w_i\}+\sum_{i\le A(t)}1\{\tau_i\le t<\tau_i+w_i\}$ for all $t\ge0$, with which the paper's proof opens. The integral is over the closed interval $[0,t]$, an atom of $F$ at $0$ included. $F$ is a probability measure $\mu$ on $\mathbb R$ with $\mu((-\infty,0))=0$. The paper's assumption that $F$ has mean $1$ is not used and is omitted, so the statement holds for every service-time distribution on $[0,\infty)$.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 8, Proposition 2.1 (proof pp. 8–9)

import Mathlib
import Definitions.Def_ReedGGN_SystemEq_NonIdling

namespace ReedGGN.SystemEq

open MeasureTheory

/-- Proposition 2.1 (p. 8): for a non-idling sample path and each `t ≥ 0`,
`Σ_{i=1}^{A(t)} (G(t − τ_i − w_i) − G(t − τ_i))
  = ∫_0^t (Q(t − s) − N)⁺ dF(s) − Σ_{i=1}^{(Q₀−N)⁺} (G(t − w̃_i) − G(t))`,
the integral over the closed interval `[0, t]`. -/
theorem proposition_2_1 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (P : SamplePath) (hP : NonIdling P) (t : ℝ) (ht : 0 ≤ t) :
    ∑ i ∈ Finset.Icc 1 (P.A t), (G μ (t - P.τ i - P.w i) - G μ (t - P.τ i)) =
      (∫ s in Set.Icc 0 t, max ((Q P (t - s) : ℝ) - P.N) 0 ∂μ) -
        ∑ i ∈ Finset.Icc 1 (P.Q₀ - P.N), (G μ (t - P.wt i) - G μ t) := by sorry

end ReedGGN.SystemEq
