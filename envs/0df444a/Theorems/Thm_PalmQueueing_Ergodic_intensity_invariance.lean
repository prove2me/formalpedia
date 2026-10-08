-- Prove2me | Theorems.Thm_PalmQueueing_Ergodic_intensity_invariance
-- name    : PalmQueueing.Ergodic.intensity_invariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T22:19:22.849983+00:00
-- url     : https://prove2.me/theorems/1038ea88-8dab-4877-b386-27b9d60f8abd
-- title:
--   Theorem 1.9.1 — invariance of the stochastic intensity
-- statement:
--   **Theorem 1.9.1.** Let $\{\mathcal{F}_t\}$ be a history of a point process $N$, and
--   suppose that both are compatible with the flow $\{\theta_t\}$. Suppose that $N$ has a non-null and
--   finite intensity $\lambda$ and let $P^0_N$ be the Palm probability associated with
--   $(N,\theta_t,P)$. Suppose that $N$ admits a $(P,\mathcal{F}_t)$-intensity $\{\lambda(t)\}$
--   compatible with the flow $\{\theta_t\}$. Then, on $\mathbb{R}_+$, $N$ admits the
--   $(P^0_N,\mathcal{F}_t)$-intensity $\{\lambda(t)\}$.
--
--   The stationary probability and the Palm probability **describe the same dynamics**. That is not
--   obvious: stochastic intensity depends on the history but also on the underlying probability, and
--   $P^0_N$ is a different probability from $P$. Remark 1.9.2 flags exactly this — "This dependence is
--   actually the main concern of Theorem 1.9.1."
--
--   The conclusion is that the intensity is **the same process** $\{\lambda(t)\}$, not merely that
--   some $(P^0_N,\mathcal{F}_t)$-intensity exists. Remark 1.9.3 writes it out: for all $(a,b] \subset
--   \mathbb{R}_+$ and $A \in \mathcal{F}_a$,
--   $$ E^0_N\big[N(a,b]\mathbf{1}_A\big] = E^0_N\Big[\Big(\int_a^b\lambda(t)dt\Big)\mathbf{1}_A\Big] .
--   \tag{1.9.1} $$
--
--   $\mathbb{R}_+$ is not a slip: the identity is asserted on the positive half-line only, since
--   $P^0_N$ puts a point at the origin and the two probabilities do not describe the same dynamics
--   across it.
--
--   Remark 1.9.1 records that under these assumptions $\{\lambda(t)\}$ can always be taken compatible
--   with the flow, and that $E[\lambda(0)] = \lambda$.
--
--   **Formalization Note.** "Compatible with the flow" for a history is the book's $\theta_t\mathcal{F}_s = \mathcal{F}_{s-t}$ (p.57), written `MeasurableSpace.comap (θ t) (H.F s) = H.F (s + t)`, i.e. $\mathbf{1}_A\circ\theta_t$ is $\mathcal{F}_{s+t}$-measurable for $A \in \mathcal{F}_s$, as the proof of Theorem 1.9.1 uses it. The joint measurability of $(t,\omega)\mapsto\theta_t\omega$ is a field of `Flow`. An $\mathcal{F}_t$-intensity is, by the definition of p.58, a non-negative *measurable* process, adapted, *locally integrable*, with $E[N(a,b]\mathbf{1}_A] = E[\int_a^b\lambda(t)dt\,\mathbf{1}_A]$ for $A\in\mathcal{F}_a$; joint measurability and ($P$-a.s.) local integrability are stated explicitly, the rest is `HasIntensity`.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 64, Theorem 1.9.1

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Palm_StochasticIntensity

/-!
# Theorem 1.9.1: invariance of the stochastic intensity (§1.9.1, p.64)
-/

namespace PalmQueueing.Ergodic

open MeasureTheory
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 1.9.1** (§1.9.1 "Invariance of Stochastic Intensity", p.64). Let `{F_t}` be a history
of a point process `N`, and suppose that both are compatible with the flow `{θ_t}`. Suppose that
`N` has a non-null and finite intensity `λ` and let `P⁰_N` be the Palm probability associated with
`(N, θ_t, P)`. Suppose that `N` admits a `(P, F_t)`-intensity `{λ(t)}` compatible with the flow
`{θ_t}`. Then, on `ℝ₊`, `N` admits the `(P⁰_N, F_t)`-intensity `{λ(t)}`.

The stationary probability and the Palm probability **describe the same dynamics**. That is the
theorem's point, and it is not obvious: stochastic intensity depends on the history but also on
the underlying probability, and `P⁰_N` is a different probability from `P`. Remark 1.9.2 flags
exactly this — "we have been more precise in the terminology (speaking for instance of the
`(P, F_t)`-intensity) because stochastic intensity depends on `{F_t}` but also, of course, on the
underlying probability. This dependence is actually the main concern of Theorem 1.9.1."

The conclusion is that the intensity is **the same process `{λ(t)}`**, not merely that some
`(P⁰_N, F_t)`-intensity exists. Remark 1.9.3 writes it out: for all `(a,b] ⊂ ℝ₊` and `A ∈ F_a`,

`(1.9.1)  E⁰_N[ N(a,b] 1_A ] = E⁰_N[ (∫_a^b λ(t)dt) 1_A ]`.

`ℝ₊` is not a slip: the identity is asserted on the positive half-line only, since `P⁰_N` puts a
point at the origin and the two probabilities do not describe the same dynamics across it.

Remark 1.9.1 records that under these assumptions `{λ(t)}` can always be taken compatible with the
flow, and that `E[λ(0)] = λ`.

`hHcompat` is "both are compatible with the flow":
`θ_t F_s = F_{s−t}` (p.57), written `comap θ_t F_s = F_{s+t}`. `hjoint` and `hloc` are the book's
definition of an `F_t`-intensity (p.58): a non-negative *measurable* process, *locally integrable*. -/
theorem intensity_invariance (S : PalmSetting Ω) (H : History Ω)
    (hhist : H.IsHistoryOf S.N)
    (hHcompat : ∀ s t : ℝ, MeasurableSpace.comap (S.θ t) (H.F s) = H.F (s + t))
    (lamProc : ℝ → Ω → ℝ)
    (hjoint : Measurable fun p : ℝ × Ω => lamProc p.1 p.2)
    (hloc : ∀ᵐ ω ∂S.P, ∀ a b : ℝ, IntegrableOn (fun t => lamProc t ω) (Set.Ioc a b) volume)
    (hcompat : IsCompatible S.θ lamProc)
    (hintensity : HasIntensity H S.N S.P lamProc) :
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → ∀ A : Set Ω, MeasurableSet[H.F a] A →
      ∫⁻ ω, Set.indicator A (fun _ => (1 : ENNReal)) ω * S.N.count ω (Set.Ioc a b) ∂S.P0
        = ∫⁻ ω, Set.indicator A (fun _ => (1 : ENNReal)) ω *
            ENNReal.ofReal (∫ t in Set.Ioc a b, lamProc t ω ∂(volume : Measure ℝ)) ∂S.P0 := by sorry

end PalmQueueing.Ergodic
