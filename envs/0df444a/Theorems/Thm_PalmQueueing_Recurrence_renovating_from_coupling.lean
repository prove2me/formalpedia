-- Prove2me | Theorems.Thm_PalmQueueing_Recurrence_renovating_from_coupling
-- name    : PalmQueueing.Recurrence.renovating_from_coupling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T00:35:51.61862+00:00
-- url     : https://prove2.me/theorems/fd019047-dd64-4b17-b9a9-2bede901cfdf
-- title:
--   Theorem 2.5.4 — the converse: coupling produces renovating events
-- statement:
--   **Theorem 2.5.4**, which the book introduces as "the following converse to Corollary
--   2.5.1 holds".
--
--   Let $\{W^{[C]}_n\}$ be a $\mathbb{R}_+^K$-valued stochastic recurrent sequence with constant
--   initial condition $C$. If $\{W^{[C]}_n\}$ couples in the strong backwards sense to
--   $\{Z \circ \theta^n\}$, where $Z$ is a finite stationary solution of $Z \circ \theta = h(Z,\xi)$,
--   then $\{W^{[C]}_n\}$ admits a $\theta$-compatible sequence of renovating events of positive
--   probability.
--
--   So Borovkov's condition is not merely sufficient. For $\mathbb{R}_+^K$-valued recurrences with a
--   constant initial condition, strong backwards coupling to a stationary solution and the existence
--   of renovating events are the same thing — which is what makes the renovating-events method a
--   characterisation rather than a technique.
--
--   **One correction to the printed page.** The book prints the conclusion for $\{W^{[0]}_n\}$; its
--   proof (p.119) builds the renovating events for $\{W^{[C]}_n\}$, namely
--   $W^{[C]}_{n+m} = g(\xi_n, \dots, \xi_{n+m-1})$ on $A_n = \theta^{-n}A$, and the printed version
--   is false: with $K = 1$, $C = 1$, $h(w,\xi) = 1$ if $w = 1$ and $w + \xi$ otherwise, and
--   $\{\xi_n\}$ i.i.d. exponential, $W^{[1]} \equiv 1$ couples with $Z \equiv 1$ while
--   $W^{[0]}_n = \xi_0 + \dots + \xi_{n-1}$ admits no renovating event of positive probability. The
--   statement is the one the proof proves, for $W^{[C]}$.
--
--   The renovating events produced are $\theta$-**compatible**, $A_n = \theta^{-n}A_0$, with $P^0(A_0) > 0$; that is exactly
--   the hypothesis Corollary 2.5.1 consumes, which is what closes the circle.
--
--   **Formalization Note.** $(P^0, \theta)$ is ergodic (§2.5.1) and $Z \circ \theta = h(Z,\xi)$
--   holds $P^0$-a.s. $\mathbb{R}_+^K$-valuedness is carried as $C \ge 0$ and $h$ mapping the
--   non-negative orthant into itself.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 118, Theorem 2.5.4

import Mathlib
import Definitions.Def_PalmQueueing_Recurrence_Renovating

/-!
# Theorem 2.5.4: the converse — coupling produces renovating events (§2.5.4, p.118)
-/

namespace PalmQueueing.Recurrence

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 2.5.4** (p.118), which the book introduces as "the following converse to Corollary
2.5.1 holds".

Let `{W_n^{[C]}}` be a `ℝ₊^K`-valued stochastic recurrent sequence with constant initial condition
`C`. If `{W_n^{[C]}}` couples in the strong backwards sense to `{Z ∘ θⁿ}`, where `Z` is a finite
stationary solution of `Z ∘ θ = h(Z, ξ)`, then `{W_n^{[C]}}` (printed: `{W_n^{[0]}}`, see below) admits a `θ`-compatible sequence of
renovating events of positive probability.

So Borovkov's condition is not merely sufficient: for `ℝ₊^K`-valued recurrences with a constant
initial condition, strong backwards coupling to a stationary solution and the existence of
renovating events are the same thing. That is what makes the renovating-events method a
characterisation rather than a technique.

**One correction to the page.** The conclusion prints `{W_n^{[0]}}`, but the proof on p.119
builds the renovating events for `{W_n^{[C]}}` (`W^{[C]}_{n+m} = g(ξ_n, …, ξ_{n+m-1})` on
`A_n = θ^{-n}A`), and with `W^{[0]}` the statement is false: for `K = 1`, `C = 1`,
`h(w, ξ) = 1` if `w = 1` and `w + ξ` otherwise, with `{ξ_n}` i.i.d. exponential, `W^{[1]} ≡ 1`
couples with `Z ≡ 1` while `W^{[0]}_n = ξ_0 + … + ξ_{n-1}` admits no renovating event of positive
probability. The item states the conclusion for `W^{[C]}`, as proved.

`herg` is the standing assumption of §2.5.1 (p.104), `(P⁰, θ)` ergodic; the stationary relation
`Z ∘ θ = h(Z, ξ)` is `P⁰`-a.s. -/
theorem renovating_from_coupling {K : ℕ} {F : Type*}
    (P0 : Measure Ω) [IsProbabilityMeasure P0] (θ : Ω ≃ᵐ Ω) (herg : Ergodic θ P0)
    (h : (Fin K → ℝ) → F → Fin K → ℝ)
    (hnonneg : ∀ (x : Fin K → ℝ) (z : F), 0 ≤ x → 0 ≤ h x z)
    (xi : ℕ → Ω → F) (xi0 : Ω → F)
    (hxi : ∀ (n : ℕ) (ω : Ω), xi n ω = xi0 ((θ : Ω → Ω)^[n] ω))
    (C : Fin K → ℝ) (hC : 0 ≤ C)
    (WC : ℕ → Ω → Fin K → ℝ)
    (hWC : IsRecurrentSequence h xi (fun _ => C) WC)
    (Z : Ω → Fin K → ℝ)
    (hZ : ∀ᵐ ω ∂P0, Z ((θ : Ω → Ω) ω) = h (Z ω) (xi0 ω))
    (hcouple : StrongBackwardsCoupling P0 θ WC Z) :
    ∃ (m : ℕ) (Phi : (Fin m → F) → Fin K → ℝ) (A : ℕ → Set Ω),
      (∀ n, MeasurableSet (A n)) ∧
      (∀ n : ℕ, A n = ((θ : Ω → Ω)^[n]) ⁻¹' A 0) ∧
      0 < P0 (A 0) ∧
      IsRenovating xi WC m Phi A := by sorry

end PalmQueueing.Recurrence
