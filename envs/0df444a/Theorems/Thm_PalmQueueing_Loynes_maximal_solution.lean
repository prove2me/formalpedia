-- Prove2me | Theorems.Thm_PalmQueueing_Loynes_maximal_solution
-- name    : PalmQueueing.Loynes.maximal_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T23:36:49.074052+00:00
-- url     : https://prove2.me/theorems/1b4b14de-9a0c-4abe-87df-49f77a158c9d
-- title:
--   Theorem 2.3.2 — the maximal stationary solution of the multiserver queue
-- statement:
--   **Theorem 2.3.2.** $V^\infty_\infty$ is finite and is the largest finite solution of
--   (2.3.2).
--
--   Unlike the single-server case, equation (2.3.2) may have several finite solutions: p.94 exhibits a
--   two-point space $\Omega = \{\omega_1, \omega_2\}$ with $s = 2$ on which a whole interval of them
--   exists. So the stationary regime of a multiserver queue is not unique. What is true is that the
--   solution set has a maximum, and it is reached by the family started above the minimal solution:
--   $V^x_0 = M_\infty + x\mathbf{1}$, $V^x_\infty = \lim_n V^x_n$, and
--   $V^\infty_\infty = \lim_{x\uparrow\infty} V^x_\infty$.
--
--   Together with the fact that $M_\infty$ is the minimal solution (p.94), this brackets the solution
--   set on both sides.
--
--   The maximality half of the proof shows that any finite solution $Z$ satisfies
--   $Z \le M_\infty + x_0 \mathbf{1}$ for some real $x_0 \ge 0$: the smallest $U \ge 0$ with
--   $Z \le M_\infty + U\mathbf{1}$ satisfies $U \ge U\circ\theta$, hence is constant by ergodicity, and
--   finite because $Z$ and $M_\infty$ are.
--
--   Finiteness is a conclusion here, not a hypothesis: the statement asserts the existence of a
--   **real-valued** process to which both limits converge, and separately that it dominates every
--   finite solution.
--
--   **Formalization Note.** All identities are between random vectors and hold $P^0$-almost surely: $M_\infty$ is given as a real random vector to which $M_n$ converges $P^0$-a.s. (Theorem 2.3.1 gives finiteness only a.s.), the two limits defining $V^\infty_\infty$ exist $P^0$-a.s., $V^\infty_\infty$ solves (2.3.2) $P^0$-a.s., and it dominates $P^0$-a.s. every measurable finite solution of (2.3.2).
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 95, Theorem 2.3.2

import Mathlib
import Definitions.Def_PalmQueueing_Loynes_MultiserverQueue

/-!
# Theorem 2.3.2: the maximal stationary solution (§2.3.3, p.95)
-/

namespace PalmQueueing.Loynes

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 2.3.2** (§2.3.3, p.95). `V^∞_∞` is finite and is the largest finite solution of
`(2.3.2)`.

Equation `(2.3.2)` may have several finite solutions — p.94 exhibits a two-point space on which a
whole interval of them exists — so the stationary regime of a multiserver queue is not unique the
way the single-server one is. What is true is that the solutions have a maximum, and it is reached
by the family `V^x_∞ = lim_n V^x_n` started from `M_∞ + x·1`: `V^x_n` is non-increasing in `n`
and non-decreasing in `x`, and `V^∞_∞ = lim_{x↑∞} V^x_∞` (2.3.14).

`M_∞` is the *minimal* solution (p.94), so the theorem bounds the solution set on both sides.

Finiteness is a conclusion, not a hypothesis: the statement asserts the existence of a
**real-valued** `V` which both limits converge to, and separately that it dominates every finite
solution. The stability hypothesis and a finite version `Mf` of `M_∞` are what §2.3.3 assumes and
are carried as hypotheses here.

Everything is `P⁰`-a.s., as for any identity between random variables: on a `P⁰`-null invariant set
(say a fixed point of `θ` with `σ = τ = 0`) every ordered non-negative vector solves (2.3.2) and
`V^x_∞ = x·1` diverges, so an "every `ω`" version would be false. The competitors `Z` are random
vectors (measurable), as the book's proof needs: it makes the smallest `U ≥ 0` with
`Z ≤ M_∞ + U·1` constant by ergodicity. -/
theorem maximal_solution {s : ℕ} (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (shift : Ω ≃ᵐ Ω) (herg : Ergodic shift P0)
    (sig tau : Ω → ℝ) (hsigmeas : Measurable sig) (htaumeas : Measurable tau)
    (hsig0 : ∀ ω, 0 ≤ sig ω) (htau0 : ∀ ω, 0 ≤ tau ω)
    (hsigInt : Integrable sig P0) (htauInt : Integrable tau P0)
    (hstab : (∫ ω, sig ω ∂P0) < (s : ℝ) * ∫ ω, tau ω ∂P0)
    (Mf : Ω → Fin s → ℝ) (hMf : IsKWLimit P0 shift sig tau Mf) :
    ∃ (Vx : ℝ → Ω → Fin s → ℝ) (V : Ω → Fin s → ℝ),
      (∀ᵐ ω ∂P0, ∀ (x : ℝ) (j : Fin s), 0 ≤ x →
        Tendsto (fun n : ℕ => kwV shift sig tau Mf x n ω j) atTop (𝓝 (Vx x ω j))) ∧
      (∀ᵐ ω ∂P0, ∀ j : Fin s, Tendsto (fun x : ℝ => Vx x ω j) atTop (𝓝 (V ω j))) ∧
      IsKWSolution P0 shift sig tau V ∧
      (∀ Z : Ω → Fin s → ℝ, Measurable Z → IsKWSolution P0 shift sig tau Z →
        ∀ᵐ ω ∂P0, ∀ j : Fin s, Z ω j ≤ V ω j) := by sorry

end PalmQueueing.Loynes
