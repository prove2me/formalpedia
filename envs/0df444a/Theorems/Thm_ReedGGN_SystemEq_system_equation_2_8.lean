-- Prove2me | Theorems.Thm_ReedGGN_SystemEq_system_equation_2_8
-- name    : ReedGGN.SystemEq.system_equation_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:12.688861+00:00
-- url     : https://prove2.me/theorems/922044f3-5984-441f-ab02-185b1b251a17
-- title:
--   (2.8), p. 9 — the system equation Q(t) = I(t) + W₀(t) + M₂(t) + A_G(t) + ∫₀ᵗ (Q(t − s) − N)⁺ dF(s) of a non-idling G/GI/N queue
-- statement:
--   Consider the $G/GI/N$ queue of §2: $N$ servers, $Q_0$ customers at time $0-$ (the first $\min(Q_0,N)$ in service with residual service times $\tilde\eta_i$, the others waiting), arrivals at times $0\le\tau_1\le\tau_2\le\cdots$ with counting process $A$, service times $\eta_i$ in order of entry into service, and waiting times $w_i$ (arrivals) and $\tilde w_i$ (initial customers $N+i$). Let $F$ be the service-time distribution, on $[0,\infty)$, with tail $G=1-F$, and $F_0$ the residual service-time distribution, on $[0,\infty)$, with tail $\bar F_0$. Let $Q(t)$ be the number in system (2.2), and $I$, $W_0$, $M_2$, $A_G$ the terms (2.4)–(2.6).
--
--   If the sample path is non-idling, then for every $t\ge 0$,
--   $$Q(t)=I(t)+W_0(t)+M_2(t)+A_G(t)+\int_0^t (Q(t-s)-N)^+\,dF(s).$$
--
--   This is the **system equation** of the $G/GI/N$ queue: the number in system equals the infinite-server terms $I+W_0+M_2+A_G$ plus a convolution of the number waiting against $F$. The paper calls it the starting point for its fluid and diffusion limits (Sections 4 and 5): written as $Q-N=x+\int_0^t(Q(t-s)-N)^+dF(s)$, it is an instance of the regulator equation (3.1).
--
--   **Formalization Note** "Non-idling" is the identity $(Q(t)-N)^+=\sum_{i\le (Q_0-N)^+}1\{t<\tilde w_i\}+\sum_{i\le A(t)}1\{\tau_i\le t<\tau_i+w_i\}$ for every $t\ge0$, which the paper uses at the start of the proof of Proposition 2.1. The integral is over the closed interval $[0,t]$, an atom of $F$ at $0$ included. $F$ and $F_0$ are probability measures on $\mathbb R$ carried by $[0,\infty)$; the paper's assumption that $F$ has mean $1$ is not used and is omitted. The statement is pathwise: it holds for every realisation, so no i.i.d. assumption appears.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 9, Eq. (2.8)

import Mathlib
import Definitions.Def_ReedGGN_SystemEq_NonIdling

namespace ReedGGN.SystemEq

open MeasureTheory

/-- The system equation (2.8) (p. 9): for a non-idling sample path of the `G/GI/N` queue and
every `t ≥ 0`,
`Q(t) = I(t) + W₀(t) + M₂(t) + A_G(t) + ∫_0^t (Q(t − s) − N)⁺ dF(s)`,
where `F` is the service-time law `μ` (carried by `[0, ∞)`), `F₀` the residual law `μ₀`
(carried by `[0, ∞)`), and the integral is over the closed interval `[0, t]`. -/
theorem system_equation_2_8 (μ μ₀ : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ₀] (hμ : μ (Set.Iio 0) = 0) (hμ₀ : μ₀ (Set.Iio 0) = 0)
    (P : SamplePath) (hP : NonIdling P) (t : ℝ) (ht : 0 ≤ t) :
    (Q P t : ℝ) =
      I μ μ₀ P t + W0 μ₀ P t + M2 μ P t + AG μ P t +
        ∫ s in Set.Icc 0 t, max ((Q P (t - s) : ℝ) - P.N) 0 ∂μ := by sorry

end ReedGGN.SystemEq
