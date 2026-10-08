-- Prove2me | Theorems.Thm_PalmQueueing_Loynes_multiserver_stability
-- name    : PalmQueueing.Loynes.multiserver_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T23:31:51.305536+00:00
-- url     : https://prove2.me/theorems/1a6efbd6-516c-415f-bf94-36e6f7d712d5
-- title:
--   Theorem 2.3.1 — stability of the G/G/s/∞ queue
-- statement:
--   **Theorem 2.3.1.** If $E^0[\sigma] < s E^0[\tau]$, then $M_\infty < \infty$ $P^0$-a.s.
--
--   $M_\infty$ is the coordinatewise limit of the non-decreasing sequence $\{M_n\}$ of ordered
--   workload vectors found by customer $0$ when customer $-n$ finds an empty system, and the book says
--   in as many words that it "has possibly infinite coordinates". So the conclusion is not a formality:
--   it is the multiserver stability criterion.
--
--   The threshold is $s E^0[\tau]$, not $E^0[\tau]$: the $s$ servers share the work, so the queue
--   tolerates $s$ times the load a single server would. The proof uses the identity
--   $(a-b)^+ = a - a\wedge b$ in (2.3.4) to get
--   $$ E^0\Big[M^1_\infty \wedge (\tau - \sigma) + \sum_{j=2}^{s} M^j_\infty \wedge \tau\Big] \le 0
--   \tag{2.3.8} $$
--   and then that $\{M^1_\infty = \infty\}$ and $\{M^s_\infty = \infty\}$ are $\theta$-contracting
--   events, so that $M^1_\infty$ is either a.s. infinite or a.s. finite; the first case contradicts
--   (2.3.8) under the stability condition.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 93, Theorem 2.3.1

import Mathlib
import Definitions.Def_PalmQueueing_Loynes_MultiserverQueue

/-!
# Theorem 2.3.1: stability of the `G/G/s/∞` queue (§2.3.2, p.93)
-/

namespace PalmQueueing.Loynes

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 2.3.1** (§2.3.2, p.93). If `E⁰[σ] < s E⁰[τ]`, then `M_∞ < ∞` `P⁰`-a.s.

`M_∞` is the coordinatewise limit of the non-decreasing sequence `{M_n}` of ordered workload
vectors found by customer `0` when customer `−n` finds an empty system, and the book is explicit
that it "has possibly infinite coordinates" — which is why `kwMinf` is `EReal`-valued and why the
conclusion `M_∞ ≠ +∞` has content.

`s E⁰[τ]` and not `E⁰[τ]`: the `s` servers share the work, and the threshold scales with them.
The proof runs through `(2.3.8)`, `E⁰[M¹_∞ ∧ (τ − σ) + Σ_{j=2}^{s} M^j_∞ ∧ τ] ≤ 0`, together with
the `θ`-contracting character of the events `{M¹_∞ = ∞}` and `{M^s_∞ = ∞}`. -/
theorem multiserver_stability {s : ℕ} (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (shift : Ω ≃ᵐ Ω) (herg : Ergodic shift P0)
    (sig tau : Ω → ℝ) (hsigmeas : Measurable sig) (htaumeas : Measurable tau)
    (hsig0 : ∀ ω, 0 ≤ sig ω) (htau0 : ∀ ω, 0 ≤ tau ω)
    (hsigInt : Integrable sig P0) (htauInt : Integrable tau P0)
    (hstab : (∫ ω, sig ω ∂P0) < (s : ℝ) * ∫ ω, tau ω ∂P0) :
    ∀ᵐ ω ∂P0, ∀ j : Fin s, kwMinf shift sig tau ω j ≠ (⊤ : EReal) := by sorry

end PalmQueueing.Loynes
