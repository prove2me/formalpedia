-- Prove2me | Theorems.Thm_TeschlODE_IVP_contraction_principle
-- name    : TeschlODE.IVP.contraction_principle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:50:34.736831+00:00
-- url     : https://prove2.me/theorems/9eb1faa2-b3cf-4b57-a512-30bae1e722ed
-- title:
--   Theorem 2.1 (Contraction principle) — unique fixed point with the estimate (2.8)
-- statement:
--   Let $X$ be a real Banach space, $C \subseteq X$ a nonempty closed subset, and $K : C \to C$ a **contraction**: there is $\theta \in [0, 1)$ with
--   $$\|K(x) - K(y)\| \le \theta \|x - y\|, \qquad x, y \in C. \qquad (2.7)$$
--   Then $K$ has a unique fixed point $\bar x \in C$, and for every starting point $x \in C$ and every $m \ge 0$
--   $$\|K^m(x) - \bar x\| \le \frac{\theta^m}{1 - \theta}\, \|K(x) - x\|. \qquad (2.8)$$
--
--   This is the Banach fixed point theorem in the form the book uses to prove the Picard–Lindelöf theorem: the a-priori estimate (2.8) bounds the distance of the $m$-th iterate from the fixed point by the size of the first step.
--
--   **Formalization Note.** The book overloads the letter $x$ in (2.8) (the fixed point on the left, an arbitrary starting point on the right); the statement names the fixed point $\bar x$. $K$ is a map $X \to X$ that sends $C$ into $C$; its values outside $C$ never enter. Uniqueness is among fixed points in $C$. $K^m$ is the $m$-fold iterate with $K^0 = \mathrm{id}$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 35, Theorem 2.1

import Mathlib

namespace TeschlODE.IVP

theorem contraction_principle {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (C : Set X) (hC : IsClosed C) (hne : C.Nonempty)
    (K : X → X) (hK : Set.MapsTo K C C) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hcontr : ∀ x ∈ C, ∀ y ∈ C, ‖K x - K y‖ ≤ θ * ‖x - y‖) :
    ∃ xbar ∈ C, K xbar = xbar ∧ (∀ y ∈ C, K y = y → y = xbar) ∧
      ∀ x ∈ C, ∀ m : ℕ, ‖K^[m] x - xbar‖ ≤ θ ^ m / (1 - θ) * ‖K x - x‖ := by sorry

end TeschlODE.IVP
