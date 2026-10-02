-- Prove2me | Theorems.Thm_TeschlODE_IVP_peano_existence
-- name    : TeschlODE.IVP.peano_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:53:37.69955+00:00
-- url     : https://prove2.me/theorems/c1d8cde9-7340-40fc-bf86-dfaf20fc14ce
-- title:
--   Theorem 2.19 (Peano) — existence of a solution for continuous f on [t₀, t₀ + T₀]
-- statement:
--   Let $f : \mathbb{R} \times \mathbb{R}^n \to \mathbb{R}^n$, $t_0 \in \mathbb{R}$, $x_0 \in \mathbb{R}^n$ and $T, \delta > 0$. Suppose $f$ is continuous on
--   $$V = [t_0, t_0 + T] \times \bar B_\delta(x_0), \qquad \bar B_\delta(x_0) = \{x : |x - x_0| \le \delta\},$$
--   and let $M = \max_{(t,x) \in V} |f(t,x)|$. Then there exists at least one solution $x$ of the initial value problem
--   $$\dot x = f(t, x), \qquad x(t_0) = x_0 \qquad (2.10)$$
--   on $[t_0, t_0 + T_0]$ which remains in $\bar B_\delta(x_0)$, where
--   $$T_0 = \min\Bigl\{T, \frac{\delta}{M}\Bigr\}, \qquad \frac{\delta}{M} = \infty \text{ if } M = 0 .$$
--   The analogous result holds for the interval $[t_0 - T_0, t_0]$, with $V = [t_0 - T, t_0] \times \bar B_\delta(x_0)$ and $M$ the maximum of $|f|$ there.
--
--   No Lipschitz condition is assumed, and uniqueness may fail (e.g. $\dot x = \sqrt{|x|}$, $x(0)=0$). This is the book's existence theorem for merely continuous right-hand sides; it is proved by Euler polygons and the Arzelà–Ascoli theorem.
--
--   **Formalization Note.** The book writes the open ball $B_\delta(x_0)$ and "the maximum of $|f|$", and says the solution "remains in $B_\delta(x_0)$". A maximum over the open ball need not exist, and the solution can reach the sphere at $t = t_0 + T_0$ (e.g. $n = 1$, $f \equiv 1$, $\delta = 1$, $T = 2$ gives $x(t) = x_0 + (t - t_0)$ with $|x(t_0 + 1) - x_0| = 1$), so the statement uses the closed ball throughout, as the book's own proof does ($|x_h(t) - x_0| \le M(t - t_0)$). $M$ is given as the greatest element of $\{|f(p)| : p \in V\}$, which exists since $V$ is compact and nonempty. $T_0$ is `if M = 0 then T else min T (δ / M)`, the book's convention $\delta/0 = \infty$. "Solution on $[t_0, t_0 + T_0]$ remaining in $\bar B_\delta(x_0)$" means: $x(t_0) = x_0$ and, for every $t$ in the interval, $(t, x(t)) \in V$ and $x$ has derivative $f(t, x(t))$ at $t$ relative to the interval (one-sided at the endpoints). The book's $V \subset U$ is not needed: $f$ is only required to be continuous on $V$. The forward and backward statements are the two conjuncts, each with its own $V$ and $M$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 56, Theorem 2.19

import Mathlib
import Definitions.Def_TeschlODE_IVP_IsSolutionOn

namespace TeschlODE.IVP

theorem peano_existence {n : ℕ}
    (f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (t₀ T δ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (hT : 0 < T) (hδ : 0 < δ) :
    -- forward in time, on `V = [t₀, t₀ + T] × B̄_δ(x₀)`
    (ContinuousOn f (Set.Icc t₀ (t₀ + T) ×ˢ Metric.closedBall x₀ δ) →
      ∀ M : ℝ,
      IsGreatest ((fun p => ‖f p‖) '' (Set.Icc t₀ (t₀ + T) ×ˢ Metric.closedBall x₀ δ)) M →
      ∃ x : ℝ → EuclideanSpace ℝ (Fin n), x t₀ = x₀ ∧
        IsSolutionOn (Set.Icc t₀ (t₀ + T) ×ˢ Metric.closedBall x₀ δ) f
          (Set.Icc t₀ (t₀ + (if M = 0 then T else min T (δ / M)))) x) ∧
    -- backward in time, on `V = [t₀ - T, t₀] × B̄_δ(x₀)`
    (ContinuousOn f (Set.Icc (t₀ - T) t₀ ×ˢ Metric.closedBall x₀ δ) →
      ∀ M : ℝ,
      IsGreatest ((fun p => ‖f p‖) '' (Set.Icc (t₀ - T) t₀ ×ˢ Metric.closedBall x₀ δ)) M →
      ∃ x : ℝ → EuclideanSpace ℝ (Fin n), x t₀ = x₀ ∧
        IsSolutionOn (Set.Icc (t₀ - T) t₀ ×ˢ Metric.closedBall x₀ δ) f
          (Set.Icc (t₀ - (if M = 0 then T else min T (δ / M))) t₀) x) := by sorry

end TeschlODE.IVP
