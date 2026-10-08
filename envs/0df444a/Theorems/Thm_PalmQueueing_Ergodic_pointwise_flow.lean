-- Prove2me | Theorems.Thm_PalmQueueing_Ergodic_pointwise_flow
-- name    : PalmQueueing.Ergodic.pointwise_flow
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T22:09:14.324946+00:00
-- url     : https://prove2.me/theorems/b8224062-a67c-44d4-bc03-246f4441db5a
-- title:
--   Theorem 1.6.4 — the continuous-time pointwise ergodic theorem
-- statement:
--   **Theorem 1.6.4 (Pointwise ergodic theorem).** Let $(\Omega,\mathcal{F},P)$ be a
--   probability space and $\{\theta_t\}$ be an ergodic flow on this space. For all $f \in L^1(P)$,
--   $$ \exists \lim_{T\to\infty} \frac{1}{T}\int_0^T f\circ\theta_t\,dt = E[f], \qquad
--   P\text{-a.s.} \tag{1.6.5} $$
--
--   The continuous-time Birkhoff theorem, quoted rather than proved: "The proof of the continuous flow
--   versions of the pointwise ergodic theorem and of the extremal characterization of ergodic flows
--   can be found in e.g. Cornfeld, Fomin and Sinai (1981)."
--
--   As in Theorem 1.6.1, the $\exists$ is part of the statement.
--
--   This is what makes the time average on the right of PASTA's (3.3.2) a well-defined object equal to
--   $E[f(Z(0))]$, and it is what the proof of Theorem 2.7.1 invokes to get
--   $\lim_{u\to-\infty}(A_{u,0} - C_{u,0}) = -\infty$. Absent from Mathlib, which has only the mean
--   ergodic theorem, and from the platform.
--
--   **Formalization Note.** The joint measurability of $(t,\omega)\mapsto\theta_t\omega$ (clause (a) of the book's flow, p.3) is a field of `Flow`; it makes $t \mapsto f(\theta_t\omega)$ measurable, so the time integral is honest.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 50, Theorem 1.6.4

import Mathlib
import Definitions.Def_PalmQueueing_Ergodic_DiscreteFlow

/-!
# Theorem 1.6.4: the continuous-time pointwise ergodic theorem (§1.6.1, p.50)
-/

namespace PalmQueueing.Ergodic

open MeasureTheory Filter Topology
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 1.6.4 (Pointwise ergodic theorem)** (p.50). Let `(Ω, F, P)` be a probability space
and `{θ_t}` be an ergodic flow on this space. For all `f ∈ L¹(P)`,

`(1.6.5)  ∃ lim_{T→∞} (1/T) ∫_0^T f ∘ θ_t dt = E[f],  P-a.s.`

The continuous-time Birkhoff theorem. The book quotes it rather than proving it: "The proof of the
continuous flow versions of the pointwise ergodic theorem and of the extremal characterization of
ergodic flows can be found in e.g. Cornfeld, Fomin and Sinai (1981)."

As in Theorem 1.6.1, the `∃` is part of the statement: the limit is asserted to exist almost
surely and to equal `E[f]`.

This is what makes the time average on the right of PASTA's `(3.3.2)` a well-defined object and
equal to `E[f(Z(0))]`, and it is what Theorem 2.7.1's proof invokes to get
`lim_{u→−∞}(A_{u,0} − C_{u,0}) = −∞`. Absent from Mathlib, which has only the mean ergodic
theorem, and from the platform.

The joint measurability of `(t, ω) ↦ θ_t ω`, clause (a) of the book's flow, is a field of `Flow`;
it is what makes `t ↦ f(θ_t ω)` measurable, so that the time integral is the book's and not the
Bochner integral's junk value `0`. -/
theorem pointwise_flow (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Flow Ω) (herg : IsErgodicFlow θ P)
    (f : Ω → ℝ) (hf : Integrable f P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun T : ℝ => (∫ t in Set.Ioc (0 : ℝ) T, f (θ t ω) ∂(volume : Measure ℝ)) / T)
      atTop (𝓝 (∫ ω, f ω ∂P)) := by sorry

end PalmQueueing.Ergodic
