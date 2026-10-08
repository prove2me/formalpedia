-- Prove2me | Theorems.Thm_PalmQueueing_Loynes_ergodic_lemma
-- name    : PalmQueueing.Loynes.ergodic_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T23:16:02.469033+00:00
-- url     : https://prove2.me/theorems/60778a23-9689-4917-800b-04fa49c05055
-- title:
--   Lemma 2.2.1 — the ergodic lemma behind Loynes' theorem
-- statement:
--   **Lemma 2.2.1.** Let $Z$ be non-negative, $P^0$-a.s. finite, and such that
--   $Z - Z \circ \theta \in L^1(P^0)$. Then $E^0[Z - Z\circ\theta] = 0$.
--
--   The book's proof is three lines: for any $C > 0$,
--   $|Z \wedge C - (Z \wedge C)\circ\theta| \le |Z - Z\circ\theta|$, and the conclusion follows from
--   $E^0[Z \wedge C - (Z\wedge C)\circ\theta] = 0$ and dominated convergence.
--
--   It is the lemma the uniqueness half of Loynes' theorem runs on. Applied to a finite solution $Z$
--   of (2.2.1), for which $Z\circ\theta - Z \le \sigma$ and $Z\circ\theta - Z \ge \sigma - \tau$
--   (2.2.15), it gives $E^0[Z\circ\theta - Z] = 0$; applied to the difference of two stationary
--   solutions it forces that difference to be $\theta$-invariant, and ergodicity then forces it to be
--   constant.
--
--   $Z$ being real-valued, "$P^0$-a.s. finite" is carried by the type. The hypothesis that is not
--   automatic and is what the lemma actually needs is the $\theta$-invariance of $P^0$, which Eq.
--   (1.2.16) of Chapter 1 supplies for the point shift.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 87, Lemma 2.2.1

import Mathlib

/-!
# Lemma 2.2.1: the ergodic lemma behind Loynes' theorem (§2.2.3, p.87)
-/

namespace PalmQueueing.Loynes

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Lemma 2.2.1** (p.87). Let `Z` be non-negative, `P⁰`-a.s. finite, and such that
`Z − Z ∘ θ ∈ L¹(P⁰)`. Then `E⁰[Z − Z ∘ θ] = 0`.

The lemma is what makes the uniqueness half of Loynes' theorem work: applied to the difference of
two stationary solutions it forces that difference to be constant, and the flow's ergodicity then
forces it to be zero. The book's own proof is three lines — for any `C > 0`,
`|Z ∧ C − (Z ∧ C) ∘ θ| ≤ |Z − Z ∘ θ|`, and the conclusion follows from
`E⁰[Z ∧ C − (Z ∧ C) ∘ θ] = 0` and dominated convergence.

`Z` is `ℝ`-valued, so "`P⁰`-a.s. finite" is carried by the type. The hypothesis that matters and is
not automatic is the `θ`-invariance of `P⁰`, which Chapter 1's Eq. (1.2.16) supplies. -/
theorem ergodic_lemma (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (shift : Ω → Ω) (hshift : Measurable shift) (hinv : Measure.map shift P0 = P0)
    (Z : Ω → ℝ) (hZmeas : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hint : Integrable (fun ω => Z ω - Z (shift ω)) P0) :
    ∫ ω, (Z ω - Z (shift ω)) ∂P0 = 0 := by sorry

end PalmQueueing.Loynes
