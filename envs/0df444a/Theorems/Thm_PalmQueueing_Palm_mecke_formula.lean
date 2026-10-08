-- Prove2me | Theorems.Thm_PalmQueueing_Palm_mecke_formula
-- name    : PalmQueueing.Palm.mecke_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T20:52:57.40811+00:00
-- url     : https://prove2.me/theorems/ccd289d4-89b3-4de2-a67d-0b5af2212d30
-- title:
--   Eq. (1.2.17) — Mecke's formula
-- statement:
--   **Mecke's formula**, the central identity of Palm calculus. For all non-negative
--   measurable functions $v$ from $(\Omega \times \mathbb{R}, \mathcal{F} \otimes \mathcal{B})$ into
--   $(\mathbb{R}, \mathcal{B})$,
--   $$ \lambda \iint_{\Omega \times \mathbb{R}} v(\omega, t)\, P^0_N(d\omega)\, dt
--   \;=\; \iint_{\Omega \times \mathbb{R}} v(\theta_t \omega, t)\, P(d\omega)\, N(\omega, dt) .
--   \tag{1.2.17} $$
--
--   The book obtains it by reading the defining formula (1.2.1) for the product function
--   $v(\omega, t) = \mathbf{1}_A(\omega)\mathbf{1}_C(t)$, and then extends it to all non-negative
--   measurable $v$ by standard monotone class arguments. It records that (1.2.17) "is known as the
--   generalized Campbell formula. In this book, it will be called Mecke's formula, after its author";
--   the original Campbell formula is the specialization $v(\omega, t) = f(t, Z_0(\omega))$ for a
--   sequence of marks $\{Z_n\}$.
--
--   The statement carries no integrability hypothesis, both sides being valued in $[0, +\infty]$. It
--   has content precisely because $P^0_N$ was defined by counting in (1.2.1) rather than as a measure
--   for which this formula holds.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 17, Eq. (1.2.17)

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Eq. (1.2.17): Mecke's formula (p.17)
-/

namespace PalmQueueing.Palm

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Mecke's formula**, Eq. (1.2.17) (p.17), the central identity of Palm calculus, which the
book also calls the generalized Campbell formula:

`λ ∫∫_{Ω × ℝ} v(ω, t) P⁰_N(dω) dt = ∫∫_{Ω × ℝ} v(θ_t ω, t) P(dω) N(ω, dt)`

for every non-negative measurable `v : (Ω × ℝ, F ⊗ B) → (ℝ, B)`. The page derives it for
`v(ω, t) = 1_A(ω) 1_C(t)` straight from the defining formula (1.2.1) of `P⁰_N` and then extends it
to all such `v` by a monotone class argument; both sides are stated here in `ℝ≥0∞`, which is where
"non-negative measurable, no integrability hypothesis" lives.

It has content precisely because `P⁰_N` is defined by counting (1.2.1) and not as "a measure
satisfying this formula". -/
theorem mecke_formula (S : PalmSetting Ω) (v : Ω → ℝ → ENNReal)
    (hv : Measurable (Function.uncurry v)) :
    ENNReal.ofReal S.lam * ∫⁻ ω, ∫⁻ t, v ω t ∂(volume : Measure ℝ) ∂S.P0
      = ∫⁻ ω, ∫⁻ t, v (S.θ t ω) t ∂(S.N.count ω) ∂S.P := by sorry

end PalmQueueing.Palm
