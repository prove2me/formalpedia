-- Prove2me | Theorems.Thm_PalmQueueing_Loynes_queueing_ergodic_theorem
-- name    : PalmQueueing.Loynes.queueing_ergodic_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T23:22:39.959266+00:00
-- url     : https://prove2.me/theorems/5f1dec51-1676-4731-a312-ccf525504276
-- title:
--   Theorem 2.2.1 — the queueing proof of the pointwise ergodic theorem
-- statement:
--   **Theorem 2.2.1.** Whenever $(P^0, \theta)$ is ergodic and both $\sigma$ and $\tau$ are
--   non-negative, not identically null, and integrable,
--   $$ \lim_{n \to \infty}
--   \frac{\sum_{i=0}^{n} \sigma \circ \theta^{-i}}{\sum_{i=0}^{n} \tau \circ \theta^{-i}}
--   \;=\; \frac{E^0[\sigma]}{E^0[\tau]} , \qquad P^0\text{-a.s.} $$
--
--   The direction of the argument is the point, and the section's title says so: "Queueing Proof of
--   the Ergodic Theorem". The queueing construction of §2.2 — Loynes' monotone scheme, Hopf's lemma
--   (2.2.18) and the stability criterion — *yields* the pointwise ergodic theorem rather than being
--   derived from it. The ratio form is what that route naturally produces, since what the queue
--   supplies is the comparison $\sum_{i=1}^n \sigma\circ\theta^{-i} \le \sum_{i=1}^n
--   \tau\circ\theta^{-i} + M_n$ with $M_n \uparrow M_\infty < \infty$ whenever
--   $E^0[\sigma] < E^0[\tau]$; a scaling argument over all $a$ with $aE^0[\sigma] < E^0[\tau]$ then
--   gives the $\limsup$ bound $E^0[\sigma]/E^0[\tau]$, and exchanging the roles of $\sigma$ and $\tau$
--   gives the matching $\liminf$.
--
--   Mathlib's `Ergodic` is reused rather than a private notion of ergodicity. Mathlib has the *mean*
--   (von Neumann) ergodic theorem but no pointwise one, so nothing here duplicates an existing
--   result.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 90, Theorem 2.2.1

import Mathlib

/-!
# Theorem 2.2.1: the queueing proof of the pointwise ergodic theorem (§2.2.5, p.90)
-/

namespace PalmQueueing.Loynes

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 2.2.1** (§2.2.5, p.90). Whenever `(P⁰, θ)` is ergodic and both `σ` and `τ` are
non-negative, not identically null, and integrable,

`lim_{n→∞} ( Σ_{i=0}^{n} σ ∘ θ^{-i} ) / ( Σ_{i=0}^{n} τ ∘ θ^{-i} ) = E⁰[σ] / E⁰[τ]`,  `P⁰`-a.s.

The section's title is "Queueing Proof of the Ergodic Theorem", and the point is the direction of
the argument: the queueing construction of §2.2 — Loynes' monotone scheme, Hopf's lemma (2.2.18)
and the stability criterion — *yields* the pointwise ergodic theorem, rather than being derived
from it. The ratio form is the natural output of that route, since what the queue supplies is the
comparison `Σ σ ∘ θ^{-i} ≤ Σ τ ∘ θ^{-i} + M_n` with `M_n ↑ M_∞ < ∞`.

Mathlib's `Ergodic` is reused rather than a private notion; Mathlib has the *mean* ergodic theorem
but no pointwise one, so nothing here duplicates it. -/
theorem queueing_ergodic_theorem (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (shift : Ω ≃ᵐ Ω) (herg : Ergodic shift P0)
    (sig tau : Ω → ℝ) (hsigmeas : Measurable sig) (htaumeas : Measurable tau)
    (hsig0 : ∀ ω, 0 ≤ sig ω) (htau0 : ∀ ω, 0 ≤ tau ω)
    (hsigNull : ¬ (∀ᵐ ω ∂P0, sig ω = 0)) (htauNull : ¬ (∀ᵐ ω ∂P0, tau ω = 0))
    (hsigInt : Integrable sig P0) (htauInt : Integrable tau P0) :
    ∀ᵐ ω ∂P0, Tendsto
      (fun n : ℕ =>
        (∑ i ∈ Finset.range (n + 1), sig ((shift.symm^[i]) ω)) /
        (∑ i ∈ Finset.range (n + 1), tau ((shift.symm^[i]) ω)))
      atTop (𝓝 ((∫ ω, sig ω ∂P0) / ∫ ω, tau ω ∂P0)) := by sorry

end PalmQueueing.Loynes
