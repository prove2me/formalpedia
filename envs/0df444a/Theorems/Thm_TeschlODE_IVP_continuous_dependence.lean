-- Prove2me | Theorems.Thm_TeschlODE_IVP_continuous_dependence
-- name    : TeschlODE.IVP.continuous_dependence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:52:13.667958+00:00
-- url     : https://prove2.me/theorems/bc546cf1-e7a9-4bb1-9704-c83f5018fc73
-- title:
--   Theorem 2.8 — continuous dependence on initial data and on the vector field, estimate (2.40)
-- statement:
--   Let $U \subseteq \mathbb{R} \times \mathbb{R}^n$ be open, $f, g$ continuous on $U$, and $f$ locally Lipschitz continuous in the second argument, uniformly with respect to the first. Let $I$ be an interval containing $t_0$, and let $x$ solve $\dot x = f(t, x)$, $x(t_0) = x_0$ and $y$ solve $\dot y = g(t, y)$, $y(t_0) = y_0$ on $I$, both with graph in $U$ (2.39). Let $V \subseteq U$ be a set containing both graphs $\{(t, x(t))\}$, $\{(t, y(t))\}$, $t \in I$, and let $L \ge 0$ and $M$ be constants with
--   $$|f(t, u) - f(t, v)| \le L|u - v| \ \text{ for } (t,u), (t,v) \in V, \qquad |f(t,u) - g(t,u)| \le M \ \text{ for } (t,u) \in V. \qquad (2.41)$$
--   Then for every $t \in I$
--   $$|x(t) - y(t)| \le |x_0 - y_0|\, e^{L|t - t_0|} + \frac{M}{L}\bigl(e^{L|t - t_0|} - 1\bigr), \qquad (2.40)$$
--   where for $L = 0$ the last term is its limit $M|t - t_0|$.
--
--   With $f = g$ this gives $|x(t) - y(t)| \le |x_0 - y_0| e^{L|t-t_0|}$ (2.43): the solution depends continuously on the initial value.
--
--   **Formalization Note.** The book defines $L$ and $M$ in (2.41) as the suprema $\sup |f(t,x) - f(t,y)|/|x-y|$ and $\sup |f - g|$ over $V$. The statement takes any constants $L \ge 0$, $M$ bounding those quotients; since the right-hand side of (2.40) is nondecreasing in $L \ge 0$ and in $M$, this is equivalent to the book's statement with the suprema when they are finite, and it avoids the Lean convention that the supremum of an unbounded set is $0$. The case $L = 0$, where the book's $M/L$ is replaced by its limit (the remark after (2.38)), is written out explicitly instead of using Lean's $M/0 = 0$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 43, Theorem 2.8

import Mathlib
import Definitions.Def_TeschlODE_IVP_IsSolutionOn
import Definitions.Def_TeschlODE_IVP_LocallyLipschitzSecond

namespace TeschlODE.IVP

theorem continuous_dependence {n : ℕ} (U : Set (ℝ × EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (f g : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) (hLip : LocallyLipschitzSecond U f)
    (I : Set ℝ) (hI : I.OrdConnected) (t₀ : ℝ) (ht₀ : t₀ ∈ I)
    (x y : ℝ → EuclideanSpace ℝ (Fin n)) (x₀ y₀ : EuclideanSpace ℝ (Fin n))
    (hx : IsSolutionOn U f I x) (hx₀ : x t₀ = x₀)
    (hy : IsSolutionOn U g I y) (hy₀ : y t₀ = y₀)
    (V : Set (ℝ × EuclideanSpace ℝ (Fin n))) (hVU : V ⊆ U)
    (hxV : ∀ t ∈ I, (t, x t) ∈ V) (hyV : ∀ t ∈ I, (t, y t) ∈ V)
    (L M : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ t : ℝ, ∀ u v : EuclideanSpace ℝ (Fin n), (t, u) ∈ V → (t, v) ∈ V →
      ‖f (t, u) - f (t, v)‖ ≤ L * ‖u - v‖)
    (hM : ∀ p ∈ V, ‖f p - g p‖ ≤ M) :
    ∀ t ∈ I, ‖x t - y t‖ ≤ ‖x₀ - y₀‖ * Real.exp (L * |t - t₀|) +
      (if L = 0 then M * |t - t₀| else M / L * (Real.exp (L * |t - t₀|) - 1)) := by sorry

end TeschlODE.IVP
