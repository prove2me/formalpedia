-- Prove2me | Theorems.Thm_TeschlODE_Frobenius_analytic_existence_uniqueness
-- name    : TeschlODE.Frobenius.analytic_existence_uniqueness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T11:17:03.636587+00:00
-- url     : https://prove2.me/theorems/9eb37f3a-a381-480a-9bbc-85786c205f03
-- title:
--   Theorem 4.1 — analytic Cauchy problem w' = f(z, w), existence and uniqueness on |z − z₀| < min(ε, δ/M)
-- statement:
--   Let $z_0, w_0 \in \mathbb{C}$, $\varepsilon, \delta > 0$, and let
--   $$\Omega = \{(z, w) \in \mathbb{C}^2 : |z - z_0| < \varepsilon,\ |w - w_0| < \delta\}.$$
--   Let $f : \Omega \to \mathbb{C}$ be analytic and bounded, and put $M = \sup_{(z,w) \in \Omega} |f(z,w)|$. Then the initial value problem
--   $$w'(z) = f(z, w(z)), \qquad w(z_0) = w_0 \qquad (4.2)$$
--   has a unique analytic solution defined on the disc $|z - z_0| < \varepsilon_0$, where
--   $$\varepsilon_0 = \min\Big(\varepsilon, \frac{\delta}{M}\Big). \qquad (4.9)$$
--
--   This is the complex Picard–Lindelöf theorem; the book's example after the theorem shows that the radius $\varepsilon_0$ cannot be improved in general.
--
--   **Formalization Note.** $f$ is a function `ℂ × ℂ → ℂ` complex differentiable on the open bidisc $\Omega$ (by Hartogs's theorem this is the same as the book's "partial complex derivatives exist"); only its values on $\Omega$ matter. $M$ is the real supremum of $|f|$ over $\Omega$, which is nonempty and, by the boundedness hypothesis `BddAbove`, bounded. When $M = 0$ the book's $\delta/M$ is read as $+\infty$, so $\varepsilon_0 = \varepsilon$ (Lean's `δ / 0 = 0` is avoided by an explicit case split). A solution on the disc $B = \{|z - z_0| < \varepsilon_0\}$ is a $w$ with $w(z_0) = w_0$ and, at every $z \in B$, $(z, w(z)) \in \Omega$ and complex derivative $w'(z) = f(z, w(z))$; such $w$ is holomorphic on $B$. Uniqueness is among all such solutions on $B$: any two agree on $B$. $\varepsilon$ is a finite real number (the book's example with $\varepsilon = \infty$ is not covered).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 113, Theorem 4.1

import Mathlib

namespace TeschlODE.Frobenius

/-- Teschl, Theorem 4.1 (p. 113): let `Ω = {(z, w) : |z − z₀| < ε, |w − w₀| < δ}` and let
`f : Ω → ℂ` be analytic and bounded, with `M = sup_Ω |f|`. Then `w' = f(z, w)`, `w(z₀) = w₀`
has a unique analytic solution on the disc `|z − z₀| < ε₀`, `ε₀ = min(ε, δ/M)` (4.9).
If `M = 0` the book's `δ/M` is read as `+∞`, so `ε₀ = ε`. A solution is required to keep its graph
in `Ω` (where `f` is defined) and to be complex differentiable with `w'(z) = f(z, w(z))` at every
point of the disc; uniqueness is among all such solutions on the disc. -/
theorem analytic_existence_uniqueness (f : ℂ × ℂ → ℂ) (z₀ w₀ : ℂ) (ε δ M ε₀ : ℝ)
    (Ω : Set (ℂ × ℂ)) (hε : 0 < ε) (hδ : 0 < δ)
    (hΩ : Ω = {x : ℂ × ℂ | ‖x.1 - z₀‖ < ε ∧ ‖x.2 - w₀‖ < δ})
    (hf : DifferentiableOn ℂ f Ω)
    (hbdd : BddAbove ((fun x => ‖f x‖) '' Ω))
    (hM : M = sSup ((fun x => ‖f x‖) '' Ω))
    (hε₀ : ε₀ = if M = 0 then ε else min ε (δ / M)) :
    ∃ w : ℂ → ℂ, w z₀ = w₀ ∧
      (∀ z ∈ Metric.ball z₀ ε₀, (z, w z) ∈ Ω ∧ HasDerivAt w (f (z, w z)) z) ∧
      ∀ v : ℂ → ℂ, v z₀ = w₀ →
        (∀ z ∈ Metric.ball z₀ ε₀, (z, v z) ∈ Ω ∧ HasDerivAt v (f (z, v z)) z) →
        ∀ z ∈ Metric.ball z₀ ε₀, v z = w z := by sorry

end TeschlODE.Frobenius
