-- Prove2me | Theorems.Thm_PalmQueueing_Ergodic_discrete_pointwise
-- name    : PalmQueueing.Ergodic.discrete_pointwise
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T21:49:20.162046+00:00
-- url     : https://prove2.me/theorems/b20cde7c-22d5-46a3-bbfd-5d7f70305cb8
-- title:
--   Theorem 1.6.1 — the discrete pointwise ergodic theorem
-- statement:
--   **Theorem 1.6.1 (Discrete pointwise ergodic theorem).** Let $(\Omega,\mathcal{F},P^0)$ be
--   a probability space and $\theta$ be a discrete ergodic flow on this space. For all $f \in
--   L^1(P^0)$,
--   $$ \exists \lim_{N\to\infty} \frac{1}{N}\sum_{1}^{N} f\circ\theta^n = E^0[f], \qquad
--   P^0\text{-a.s.} \tag{1.6.1} $$
--
--   This is **Birkhoff's theorem**, which the book quotes rather than proves — though the proof it
--   points to is its own: "A proof of this theorem based on Loynes' construction can be found in
--   §2.2.5, Chapter 2", which is Theorem 2.2.1 of this series' mission II.
--
--   The $\exists$ in the display is part of the statement: the limit is asserted to **exist** almost
--   surely and to equal $E^0[f]$, not merely to equal it wherever it happens to exist.
--
--   It is worth stating because the substrate is absent everywhere. Mathlib has the *mean* (von
--   Neumann, $L^2$) ergodic theorem in `Analysis/InnerProductSpace/MeanErgodic` but no pointwise one,
--   and the platform has neither. The attribution to Birkhoff belongs in the prose; the `source` cites
--   Baccelli's page, because that is where this mission read it.
--
--   **Formalization Note.** A discrete flow is, by the book's definition on p.46, "a bijective and measurable map from $\Omega$ to itself, which preserves $P^0$"; the statement carries `Function.Bijective θ` alongside Mathlib's `Ergodic θ P0` (measure preserving and pre-ergodic).
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 47, Theorem 1.6.1

import Mathlib
import Definitions.Def_PalmQueueing_Ergodic_DiscreteFlow

/-!
# Theorem 1.6.1: the discrete pointwise ergodic theorem (§1.6.1, p.47)
-/

namespace PalmQueueing.Ergodic

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 1.6.1 (Discrete pointwise ergodic theorem)** (p.47). Let `(Ω, F, P⁰)` be a
probability space and `θ` be a discrete ergodic flow on this space. For all `f ∈ L¹(P⁰)`,

`(1.6.1)  ∃ lim_{N→∞} (1/N) Σ_{n=1}^{N} f ∘ θⁿ = E⁰[f],  P⁰-a.s.`

**This is Birkhoff's theorem, which the book quotes rather than proves.** The proof it points to is
its own: "A proof of this theorem based on Loynes' construction can be found in §2.2.5, Chapter 2"
— which is Theorem 2.2.1 of mission `02a`, the queueing proof of the ergodic theorem.

The `∃` in the display is part of the statement: the limit is asserted to **exist** almost surely
and to equal `E⁰[f]`, not merely to equal it where it exists.

It is stated here because the substrate is absent everywhere: Mathlib has the *mean* (von Neumann,
`L²`) ergodic theorem in `Analysis/InnerProductSpace/MeanErgodic` but no pointwise one, and the
platform has neither. The `source` cites Baccelli's page, since that is where this mission read
it; the attribution to Birkhoff belongs in the prose.

`hbij` is the book's definition of a discrete flow (p.46): "a bijective and measurable map from
`Ω` to itself, which preserves `P⁰`". -/
theorem discrete_pointwise (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (θ : Ω → Ω) (hθ : Measurable θ) (hbij : Function.Bijective θ) (herg : Ergodic θ P0)
    (f : Ω → ℝ) (hf : Integrable f P0) :
    ∀ᵐ ω ∂P0, Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, f (θ^[n] ω)) / (N : ℝ))
      atTop (𝓝 (∫ ω, f ω ∂P0)) := by sorry

end PalmQueueing.Ergodic
