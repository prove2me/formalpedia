-- Prove2me | Theorems.Thm_TeschlODE_IVP_weissinger
-- name    : TeschlODE.IVP.weissinger
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:51:33.810817+00:00
-- url     : https://prove2.me/theorems/de83b9d5-9e06-4c4e-b8dc-9d8f1d3fe71d
-- title:
--   Theorem 2.4 (Weissinger) — fixed point for summable iterate constants, estimate (2.22)
-- statement:
--   Let $X$ be a real Banach space, $C \subseteq X$ nonempty and closed, and $K : C \to C$. Suppose there are numbers $\theta_m$, $m \ge 1$, with
--   $$\|K^m(x) - K^m(y)\| \le \theta_m \|x - y\|, \qquad x, y \in C,\ m \ge 1, \qquad (2.21)$$
--   and $\sum_{m \ge 1} \theta_m < \infty$. Then $K$ has a unique fixed point $\bar x \in C$, and for every $x \in C$ and every $m \ge 1$
--   $$\|K^m(x) - \bar x\| \le \Bigl(\sum_{j = m}^{\infty} \theta_j\Bigr) \|K(x) - x\|. \qquad (2.22)$$
--
--   This generalises the contraction principle (Theorem 2.1, $\theta_m = \theta^m$); it is what removes the restriction $T_0 < L^{-1}$ from the proof of the Picard–Lindelöf theorem.
--
--   **Formalization Note.** $\theta$ is a real sequence indexed by $\mathbb{N}$; (2.21) and (2.22) are required only for $m \ge 1$, as in the book (whose sum starts at $n = 1$), so the value $\theta_0$ never matters. "$\sum \theta_m < \infty$" is `Summable θ` (for real sequences this is absolute summability; the $\theta_m$ are nonnegative whenever $C$ has two points). The fixed point is named $\bar x$ (the book overloads $x$). $K$ is a map $X \to X$ sending $C$ into $C$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 39, Theorem 2.4

import Mathlib

namespace TeschlODE.IVP

theorem weissinger {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (C : Set X) (hC : IsClosed C) (hne : C.Nonempty)
    (K : X → X) (hK : Set.MapsTo K C C) (θ : ℕ → ℝ)
    (hθ : ∀ m : ℕ, 1 ≤ m → ∀ x ∈ C, ∀ y ∈ C, ‖K^[m] x - K^[m] y‖ ≤ θ m * ‖x - y‖)
    (hsum : Summable θ) :
    ∃ xbar ∈ C, K xbar = xbar ∧ (∀ y ∈ C, K y = y → y = xbar) ∧
      ∀ x ∈ C, ∀ m : ℕ, 1 ≤ m →
        ‖K^[m] x - xbar‖ ≤ (∑' j : ℕ, θ (m + j)) * ‖K x - x‖ := by sorry

end TeschlODE.IVP
