-- Prove2me | Theorems.Thm_RobinsonNSIFT_Implicit_lemma_3_1
-- name    : RobinsonNSIFT.Implicit.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:02:42.267977+00:00
-- url     : https://prove2.me/theorems/30f001bd-2714-4272-aff1-64a5723a6689
-- title:
--   Lemma 3.1 — Lipschitz perturbation lemma: f + h stays onto a ball and δ(f + h, Ω) ≥ δ − η
-- statement:
--   This is the Lipschitz analogue of the Banach perturbation lemma for linear operators.
--
--   Let $(X, d)$ be a complete metric space, $\Omega$ an open subset of $X$, and $Y$ a real normed linear space. Let $f, h : \Omega \to Y$, with $h$ Lipschitzian on $\Omega$ with modulus $\eta \ge 0$. Let $x_0 \in \Omega$ and $y_0 = f(x_0)$. Write $B(x, \rho)$ for the closed ball of radius $\rho$ about $x$. Let $\alpha$ be a real number and $\delta$ a real number with $d(f(x_1), f(x_2)) \ge \delta\, d(x_1, x_2)$ for all $x_1, x_2 \in \Omega$ (i.e. $\delta \le \delta(f,\Omega)$). Assume that
--
--   1. $f(\Omega) \supseteq B(y_0, \alpha)$;
--   2. $\eta < \delta$;
--   3. $\Omega \supseteq B(x_0, \delta^{-1}\alpha)$;
--   4. $\theta := (1 - \eta\delta^{-1})\alpha - \|h(x_0)\| \ge 0$.
--
--   Then
--   $$
--   (f+h)\big(B(x_0, \delta^{-1}\alpha)\big) \supseteq B(y_0, \theta), \qquad \delta(f+h, \Omega) \ge \delta - \eta > 0 .
--   $$
--
--   So a map whose inverse is Lipschitzian, perturbed by a Lipschitzian map of smaller modulus, keeps a Lipschitzian inverse and still covers a ball. Robinson uses it to solve $F(x, y) = 0$ for each fixed $y$ in the proof of Theorem 3.2.
--
--   **Formalization Note** The paper states the lemma with $\delta := \delta(f, \Omega)$. Here $\delta$ is any real lower bound of $\delta(f,\Omega)$ (`ExpansionAtLeast f Ω δ`), and the second conclusion is `ExpansionAtLeast (f + h) Ω (δ - η)`. This is equivalent to the paper's statement: taking $\delta = \delta(f,\Omega)$ recovers it, and conversely the paper's lemma applied with $\delta(f,\Omega) \ge \delta$ yields the conclusion for $\delta$ (smaller domain ball, larger $\theta$, larger lower bound). The paper's hypothesis $0 \le \eta$ is built into the type: $\eta$ is a nonnegative real. $f$ and $h$ are total functions on $X$, constrained on $\Omega$ only. Openness of $\Omega$ is kept exactly as printed. The radius $\delta^{-1}\alpha$ is written `α / δ`.
-- source:
--   Robinson, An Implicit-Function Theorem for a Class of Nonsmooth Functions, Math. Oper. Res. 16(2) (1991), Lemma 3.1, p. 298

import Mathlib
import Definitions.Def_RobinsonNSIFT_Implicit_Basic

open Set Metric
open scoped NNReal

namespace RobinsonNSIFT.Implicit

theorem lemma_3_1 {X Y : Type*} [MetricSpace X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Ω : Set X) (hΩ : IsOpen Ω) (f h : X → Y) (η : ℝ≥0) (hh : LipschitzOnWith η h Ω)
    (x₀ : X) (hx₀ : x₀ ∈ Ω) (y₀ : Y) (hfx₀ : f x₀ = y₀) (α δ : ℝ)
    (hδ : ExpansionAtLeast f Ω δ)
    (h1 : closedBall y₀ α ⊆ f '' Ω)
    (h2 : (η : ℝ) < δ)
    (h3 : closedBall x₀ (α / δ) ⊆ Ω)
    (h4 : 0 ≤ (1 - η / δ) * α - ‖h x₀‖) :
    closedBall y₀ ((1 - η / δ) * α - ‖h x₀‖) ⊆ (f + h) '' closedBall x₀ (α / δ) ∧
      ExpansionAtLeast (f + h) Ω (δ - η) ∧ 0 < δ - η := by sorry

end RobinsonNSIFT.Implicit
