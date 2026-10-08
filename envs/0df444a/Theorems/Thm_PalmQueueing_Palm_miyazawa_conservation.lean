-- Prove2me | Theorems.Thm_PalmQueueing_Palm_miyazawa_conservation
-- name    : PalmQueueing.Palm.miyazawa_conservation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T21:23:40.05337+00:00
-- url     : https://prove2.me/theorems/e89f4716-83fd-475c-ae64-059fd4725dc3
-- title:
--   Eq. (1.3.10) — the Miyazawa (rate) conservation principle
-- statement:
--   **The Miyazawa conservation principle.** Let $\{Y(t)\}$ be a bounded real-valued
--   stochastic process, right-continuous with left-hand limits, and compatible with the flow
--   $\{\theta_t\}$. Let $N$ be a point process compatible with $\{\theta_t\}$ and with non-null finite
--   intensity $\lambda$, and let $\{Y'(t)\}$ be a real-valued stochastic process compatible with
--   $\{\theta_t\}$ and such that
--   $$ Y(1) = Y(0) + \int_0^1 Y'(s)\,ds + \int_{(0,1]} \big(Y(s) - Y(s-)\big)\, N(ds) \tag{1.3.9} $$
--   (for instance $N$ counts all the discontinuity points of $\{Y(t)\}$ and $Y'(t)$ is the derivative
--   of $Y(t)$ between discontinuity points). Taking expectations on both sides and using the
--   $\theta_t$-invariance of $P$ gives **Miyazawa's formula**
--   $$ E[Y'(0)] + \lambda E^0_N[Y(0) - Y(0-)] = 0 . \tag{1.3.10} $$
--
--   The mean drift of the continuous part is exactly cancelled by the mean jump rate: this is the
--   *(rate) conservation principle*, applied many times in Chapter 3.
--
--   Boundedness of $\{Y(t)\}$ is the hypothesis the book states. Remark 1.3.4 on p.24 observes that it
--   can be replaced by any one of three integrability conditions; those are recorded in the mission's
--   moderation notes rather than stated here, so that the item is the book's theorem and not a
--   strengthening of it.
--
--   **Formalization Note.** Formula (1.3.10) treats $E[Y'(0)]$ as a finite number, so the item assumes
--   $Y'(0) \in L^1(P)$. Lean's Bochner integral of a non-integrable function is $0$, and without this
--   hypothesis the statement would be false: with $Y(t) = \sin(Ut + V) + (t - T_0(t))$ over a lattice
--   point process of random phase and $U$ heavy-tailed ($E|U| = \infty$), (1.3.9) holds pathwise while
--   the Lean value of $E[Y'(0)]$, for $Y'(0) = U\cos V + 1$, is $0$ and $\lambda E^0_N[Y(0) - Y(0-)] = -1$.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, pp. 23-24, §1.3.3, Eqs. (1.3.9)-(1.3.10)

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Eq. (1.3.10): the Miyazawa (rate) conservation principle (§1.3.3, pp.23-24)
-/

namespace PalmQueueing.Palm

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The Miyazawa conservation principle**, Eq. (1.3.10) (§1.3.3, p.24). Let `{Y(t)}` be a
bounded real-valued corlol process compatible with the flow `{θ_t}`, let `N` be a point process
compatible with `{θ_t}` with non-null finite intensity `λ`, and let `{Y'(t)}` be a real-valued
process compatible with `{θ_t}` such that

`(1.3.9)  Y(1) = Y(0) + ∫_0^1 Y'(s) ds + ∫_{(0,1]} (Y(s) - Y(s-)) N(ds)`

— for instance `N` counts the discontinuity points of `{Y(t)}` and `Y'(t)` is the derivative of
`Y(t)` between them. Then

`(1.3.10)  E[Y'(0)] + λ E⁰_N[ Y(0) - Y(0-) ] = 0`:

the mean drift of the continuous part is exactly cancelled by the mean jump rate. This is the
*(rate) conservation principle*, which Chapter 3 applies repeatedly.

The boundedness of `{Y(t)}` is the hypothesis the book states; Remark 1.3.4 on p.24 records three
alternatives to it, recorded in `MODERATION_NOTES.md` rather than stated here. `hY'int` makes
explicit that `E[Y'(0)]` in (1.3.10) is a finite expectation, as the book's formula presupposes:
without it a Bochner integral of a non-integrable `Y'(0)` would silently read as `0`. -/
theorem miyazawa_conservation (S : PalmSetting Ω) (Y Yl Y' : ℝ → Ω → ℝ)
    (hYbdd : ∃ C : ℝ, ∀ (t : ℝ) (ω : Ω), |Y t ω| ≤ C)
    (hYmeas : ∀ t, Measurable (Y t)) (hYlmeas : ∀ t, Measurable (Yl t))
    (hY'meas : ∀ t, Measurable (Y' t)) (hY'int : Integrable (Y' 0) S.P)
    (hYright : ∀ (s : ℝ) (ω : Ω), ContinuousWithinAt (fun u => Y u ω) (Set.Ici s) s)
    (hYleft : IsLeftLimitProcess Y Yl)
    (hYcomp : IsCompatible S.θ Y) (hY'comp : IsCompatible S.θ Y')
    (hjump : ∀ ω, Y 1 ω = Y 0 ω + (∫ s in Set.Ioc (0 : ℝ) 1, Y' s ω ∂(volume : Measure ℝ))
        + ∫ s in Set.Ioc (0 : ℝ) 1, (Y s ω - Yl s ω) ∂(S.N.count ω)) :
    (∫ ω, Y' 0 ω ∂S.P) + S.lam * ∫ ω, (Y 0 ω - Yl 0 ω) ∂S.P0 = 0 := by sorry

end PalmQueueing.Palm
