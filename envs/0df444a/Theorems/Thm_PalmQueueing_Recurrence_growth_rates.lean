-- Prove2me | Theorems.Thm_PalmQueueing_Recurrence_growth_rates
-- name    : PalmQueueing.Recurrence.growth_rates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T00:44:29.332986+00:00
-- url     : https://prove2.me/theorems/0ed8bf9b-506a-4e3b-a46d-446b3b421fe1
-- title:
--   Theorem 2.11.2 — asymptotic growth rates of a monotone–homogeneous recurrence
-- statement:
--   **Theorem 2.11.2.** For all monotone and homogeneous stochastic recurrences such that for
--   all $n$, $X^{[0]}_n$ is integrable and $E[X^{[0]}_n] > -Cn$ for some positive $C$, there exist
--   constants $\overline{\gamma}, \underline{\gamma} \in \mathbb{R}$ such that for all
--   $Y \in \mathbb{R}^K$ with $E^0[\|Y\|_\infty] < \infty$,
--   $$ \lim_n \frac{\max_i (X^{[Y]}_n)^i}{n} = \overline{\gamma}\ \ P^0\text{-a.s.}, \qquad
--   \lim_n \frac{E^0[\max_i (X^{[Y]}_n)^i]}{n} = \overline{\gamma} , \tag{2.11.6} $$
--   $$ \lim_n \frac{\min_i (X^{[Y]}_n)^i}{n} = \underline{\gamma}\ \ P^0\text{-a.s.}, \qquad
--   \lim_n \frac{E^0[\min_i (X^{[Y]}_n)^i]}{n} = \underline{\gamma} . \tag{2.11.7} $$
--
--   **Four limits, not two.** Each of (2.11.6) and (2.11.7) asserts both an almost-sure limit and the
--   corresponding limit of expectations, and both constants are named. Stating only the maximum, or
--   only the almost-sure halves, would be a strictly weaker theorem; the $L^1$ halves are what the
--   saturation rule of §2.11.4 goes on to use.
--
--   The hypothesis $E[X^{[0]}_n] > -Cn$ is a **one-sided linear lower bound**, not an integrability
--   condition — integrability is assumed separately — and it is what rules out the growth rate being
--   $-\infty$.
--
--   The proof, for $Y = 0$, is Property 2.11.2 and Kingman's sub-additive ergodic theorem
--   (Theorem 1.6.2 of Chapter 1). For any other finite initial condition $Y$, Exercise 2.11.3 gives
--   $\lim_n X^{[Y]}_n/n = \lim_n X^{[0]}_n/n$ $P^0$-a.s., and the $L^1$ limit follows in the same way.
--
--   **Formalization Note.** $Y$ ranges over $\mathbb{R}^K$-valued random variables with
--   $E^0[\|Y\|_\infty] < \infty$ (`Integrable Y`, the norm on `Fin K → ℝ` being the sup norm); the
--   driving variables are measurable and $h$ is measurable in $\xi$. $\max_i$ and $\min_i$ are the
--   finite `⨆`/`⨅` over `Fin K`.
--
--   Example 2.11.3 applies it to the multiserver queue of §2.2.3: the limit
--   $\lim_n \max_i X^i_n/n = \overline{\gamma}$ exists and is positive and finite **whether or not**
--   the stability condition $E^0[\sigma] < sE^0[\tau]$ holds, and since $\max_i X^i_n = T_n + W^s_n$,
--   $\lim_n W^s_n/n = \overline{\gamma} - \lambda^{-1}$ $P^0$-a.s.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 158, Theorem 2.11.2

import Mathlib
import Definitions.Def_PalmQueueing_Recurrence_MonotoneHomogeneous

/-!
# Theorem 2.11.2: asymptotic growth rates of a monotone-homogeneous recurrence (§2.11.2, p.158)
-/

namespace PalmQueueing.Recurrence

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 2.11.2** (p.158). For all monotone and homogeneous stochastic recurrences such that
for all `n`, `X_n^{[0]}` is integrable and `E[X_n^{[0]}] > −Cn` for some positive `C`, there exist
constants `γ̄, γ_ ∈ ℝ` such that for all `Y ∈ ℝ^K` with `E⁰[‖Y‖_∞] < ∞`,

`(2.11.6)  lim_n max_i (X_n^{[Y]})^i / n = γ̄  P⁰-a.s.,   lim_n E⁰[max_i (X_n^{[Y]})^i] / n = γ̄`,

`(2.11.7)  lim_n min_i (X_n^{[Y]})^i / n = γ_  P⁰-a.s.,  lim_n E⁰[min_i (X_n^{[Y]})^i] / n = γ_`.

**Four limits, not two.** Each of (2.11.6) and (2.11.7) asserts both an almost-sure limit and the
corresponding limit of expectations, and both constants are named. Stating only the maximum, or
only the a.s. halves, would be a strictly weaker theorem; the `L¹` halves are what the saturation
rule of §2.11.4 later uses.

The hypothesis `E[X_n^{[0]}] > −Cn` is a **one-sided linear lower bound**, not an integrability
condition: integrability is assumed separately. It is what rules out the growth rate being `−∞`.

`Y` ranges over `ℝ^K`-valued **random variables** with `E⁰[‖Y‖_∞] < ∞`, i.e. `Integrable Y P⁰`
(the norm on `Fin K → ℝ` is the sup norm); `{ξ_n}` are random variables and `h` is measurable in
`ξ`, as the section's setting requires.

The proof is Kingman's sub-additive ergodic theorem for `Y = 0`, plus the fact that the limit does
not depend on the finite initial condition. -/
theorem growth_rates {K : ℕ} {F : Type*} [MeasurableSpace F] (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (θ : Ω ≃ᵐ Ω) (herg : Ergodic θ P0)
    (h : (Fin K → ℝ) → F → Fin K → ℝ) (hMH : IsMHRecurrence h)
    (hh : ∀ x : Fin K → ℝ, Measurable (h x))
    (xi : ℕ → Ω → F) (xi0 : Ω → F) (hxi0 : Measurable xi0)
    (hxi : ∀ (n : ℕ) (ω : Ω), xi n ω = xi0 ((θ : Ω → Ω)^[n] ω))
    (hint : ∀ n : ℕ, ∀ i : Fin K,
      Integrable (fun ω => mhIterate h xi (fun _ => (0 : Fin K → ℝ)) n ω i) P0)
    (Cst : ℝ) (hCst : 0 < Cst)
    (hlb : ∀ n : ℕ, ∀ i : Fin K,
      -(Cst * n) < ∫ ω, mhIterate h xi (fun _ => (0 : Fin K → ℝ)) n ω i ∂P0) :
    ∃ gbar glow : ℝ, ∀ Y : Ω → Fin K → ℝ, Integrable Y P0 →
      ((∀ᵐ ω ∂P0, Tendsto
          (fun n : ℕ => (⨆ i : Fin K, mhIterate h xi Y n ω i) / (n : ℝ)) atTop (𝓝 gbar)) ∧
       Tendsto
          (fun n : ℕ => (∫ ω, (⨆ i : Fin K, mhIterate h xi Y n ω i) ∂P0) / (n : ℝ))
          atTop (𝓝 gbar)) ∧
      ((∀ᵐ ω ∂P0, Tendsto
          (fun n : ℕ => (⨅ i : Fin K, mhIterate h xi Y n ω i) / (n : ℝ)) atTop (𝓝 glow)) ∧
       Tendsto
          (fun n : ℕ => (∫ ω, (⨅ i : Fin K, mhIterate h xi Y n ω i) ∂P0) / (n : ℝ))
          atTop (𝓝 glow)) := by sorry

end PalmQueueing.Recurrence
