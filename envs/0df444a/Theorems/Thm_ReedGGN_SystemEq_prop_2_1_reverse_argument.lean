-- Prove2me | Theorems.Thm_ReedGGN_SystemEq_prop_2_1_reverse_argument
-- name    : ReedGGN.SystemEq.prop_2_1_reverse_argument
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:56.017562+00:00
-- url     : https://prove2.me/theorems/493b9cd1-9816-4f1a-920d-0f3eeafeeced
-- title:
--   Proof of Proposition 2.1, the reverse argument (p. 9) — ∫₀ᵗ Σ 1{w̃ᵢ > t − s} dF(s) = Σ (G(t − w̃ᵢ) − G(t))
-- statement:
--   Let $F$ be a service-time distribution on $[0,\infty)$ with tail $G=1-F$, and fix a sample path of the $G/GI/N$ queue with $N$ servers, $Q_0$ initial customers and nonnegative waiting times $\tilde w_i$ of the initial customers $N+i$. Then for every $t\ge 0$,
--   $$\int_0^t\sum_{i=1}^{(Q_0-N)^+}1\{\tilde w_i>t-s\}\,dF(s)=\sum_{i=1}^{(Q_0-N)^+}\big(G(t-\tilde w_i)-G(t)\big).$$
--
--   This is the last step of the proof of Proposition 2.1: it converts the contribution of the initial waiting customers to $\int_0^t (Q(t-s)-N)^+\,dF(s)$ back into tails of $F$.
--
--   **Formalization Note** The integral is over the closed interval $[0,t]$, an atom of $F$ at $0$ included. $F$ is a probability measure $\mu$ on $\mathbb R$ with $\mu((-\infty,0))=0$, and $G(x)=\mu((x,\infty))$ for every real $x$.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 9, proof of Proposition 2.1 ("A reverse argument can now also be used to show that")

import Mathlib
import Definitions.Def_ReedGGN_SystemEq_QueueLength

namespace ReedGGN.SystemEq

open MeasureTheory

/-- Proof of Proposition 2.1, the reverse argument (p. 9):
`∫_0^t Σ_{i=1}^{(Q₀−N)⁺} 1{w̃_i > t − s} dF(s) = Σ_{i=1}^{(Q₀−N)⁺} (G(t − w̃_i) − G(t))`,
the integral over the closed interval `[0, t]`. -/
theorem prop_2_1_reverse_argument (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (P : SamplePath) (t : ℝ) (ht : 0 ≤ t) :
    ∫ s in Set.Icc 0 t,
        (∑ i ∈ Finset.Icc 1 (P.Q₀ - P.N), if t - s < P.wt i then (1 : ℝ) else 0) ∂μ =
      ∑ i ∈ Finset.Icc 1 (P.Q₀ - P.N), (G μ (t - P.wt i) - G μ t) := by sorry

end ReedGGN.SystemEq
