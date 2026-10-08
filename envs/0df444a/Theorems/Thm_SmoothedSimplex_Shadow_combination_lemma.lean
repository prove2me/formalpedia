-- Prove2me | Theorems.Thm_SmoothedSimplex_Shadow_combination_lemma
-- name    : SmoothedSimplex.Shadow.combination_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:47:33.605914+00:00
-- url     : https://prove2.me/theorems/c3bf2c4f-44c8-43cc-bc8c-fd516c64ac90
-- title:
--   Lemma 2.3.5 — combination lemma: $\Pr[F(x)G(x,y)\le\varepsilon]\le 4\alpha\beta\varepsilon$
-- statement:
--   Let $x$ and $y$ be random variables with joint distribution $\mu(x,y)$. Let $F(x)$ and $G(x,y)$ be non-negative measurable functions and $\alpha,\beta\ge0$ constants such that
--
--   1. for all $\varepsilon\ge0$, $\Pr_{x,y}[F(x)\le\varepsilon]\le\alpha\varepsilon$, and
--   2. for all $\varepsilon\ge0$, $\max_x\Pr_y[G(x,y)\le\varepsilon]\le(\beta\varepsilon)^2$, where $y$ is distributed according to the induced (conditional) distribution given $x$.
--
--   Then for all $\varepsilon\ge0$
--
--   $$
--   \Pr_{x,y}\big[F(x)\,G(x,y)\le\varepsilon\big]\le 4\alpha\beta\varepsilon .
--   $$
--
--   The lemma combines a linear small-ball bound and a quadratic one into a linear small-ball bound for the product; it is how the distance and angle estimates of Section 4 are put together.
--
--   **Formalization Note** The joint law is written $\nu\otimes\kappa$, with $\nu$ the law of $x$ (a probability measure) and $\kappa$ a Markov kernel giving the conditional law of $y$ given $x$; "$\max_x$" is "for every $x$". The non-negativity of $\beta$ is implicit on the page (for $\beta<0$ the hypothesis only involves $\beta^2$).
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 2.3.5, printed p. 17 (PDF p. 17)

import Mathlib

namespace SmoothedSimplex.Shadow

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- **Lemma 2.3.5 (Combination lemma)** (Spielman & Teng, arXiv:cs/0111050v7, Lemma 2.3.5,
printed p. 17, PDF p. 17). Let `x` and `y` be random variables distributed according to
`µ(x, y)`. Let `F(x)` and `G(x, y)` be non-negative functions and `α` and `β` be constants such
that `∀ ε ≥ 0, Pr_{x,y}[F(x) ≤ ε] ≤ αε`, and `∀ ε ≥ 0, max_x Pr_y[G(x, y) ≤ ε] ≤ (βε)²`, where in
the second line `y` is distributed according to the induced density. Then
`Pr_{x,y}[F(x)G(x, y) ≤ ε] ≤ 4αβε`.

**Formalization Note.**
* The joint law `µ` is written `ν ⊗ₘ κ`: `ν` is the law of `x` and the Markov kernel `κ` gives
  the induced (conditional) law of `y` given `x`. "`max_x`" is "for every `x`".
* `F`, `G` are measurable, and the constants are non-negative (`α ≥ 0` is forced by the first
  hypothesis; `β ≥ 0` is implicit on the page — for `β < 0` the hypothesis only sees `β²`
  while the conclusion would have a negative right-hand side).
* The conclusion holds for every `ε ≥ 0`. -/
theorem combination_lemma {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [IsProbabilityMeasure ν] (κ : Kernel X Y) [IsMarkovKernel κ]
    (F : X → ℝ) (G : X → Y → ℝ) (hF : Measurable F) (hG : Measurable (Function.uncurry G))
    (hF0 : ∀ x, 0 ≤ F x) (hG0 : ∀ x y, 0 ≤ G x y) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h1 : ∀ ε : ℝ, 0 ≤ ε → (ν ⊗ₘ κ) {p | F p.1 ≤ ε} ≤ ENNReal.ofReal (α * ε))
    (h2 : ∀ ε : ℝ, 0 ≤ ε → ∀ x, κ x {y | G x y ≤ ε} ≤ ENNReal.ofReal ((β * ε) ^ 2)) :
    ∀ ε : ℝ, 0 ≤ ε →
      (ν ⊗ₘ κ) {p | F p.1 * G p.1 p.2 ≤ ε} ≤ ENNReal.ofReal (4 * α * β * ε) := by sorry

end SmoothedSimplex.Shadow
