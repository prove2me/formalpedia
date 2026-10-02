-- Prove2me | Theorems.Thm_TeschlODE_Linear_exists_unique_solution
-- name    : TeschlODE.Linear.exists_unique_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:54:59.583782+00:00
-- url     : https://prove2.me/theorems/bcfe15d6-30da-42e7-8ed5-67128f45005e
-- title:
--   Theorem 3.9 — global existence and uniqueness for ẋ = A(t)x
-- statement:
--   Let $I \subseteq \mathbb{R}$ be an interval, $A \in C(I, \mathbb{R}^{n\times n})$, $t_0 \in I$ and $x_0 \in \mathbb{R}^n$. Then the linear system
--   $$\dot x(t) = A(t)x(t), \qquad x(t_0) = x_0,$$
--   has a solution defined on all of $I$, and any two solutions on $I$ with the same initial value agree on $I$.
--
--   This is the linear case of the Picard–Lindelöf theory of Chapter 2; the point of the theorem is that no blow-up occurs, so the solution lives on the whole interval on which $A$ is continuous.
--
--   **Formalization Note.** "Interval" is `Set.OrdConnected I` (any kind of interval, bounded or not, open, closed or half-open); continuity is `ContinuousOn A I`. Existence on all of $I$ and uniqueness are stated together: existence of an `IsSolution A I x` with `x t₀ = x₀`, and every other such solution coincides with it on $I$ (`Set.EqOn`).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 81, Theorem 3.9

import Mathlib
import Definitions.Def_TeschlODE_Linear_IsSolution

namespace TeschlODE.Linear

/-- Teschl, Theorem 3.9 (p. 81): for `A ∈ C(I, ℝ^{n×n})` on an interval `I` and `t₀ ∈ I`, the
system (3.79) has a unique solution with `x(t₀) = x₀`, and it is defined on all of `I`. -/
theorem exists_unique_solution {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (I : Set ℝ)
    (hI : I.OrdConnected) (hA : ContinuousOn A I) (t₀ : ℝ) (ht₀ : t₀ ∈ I) (x₀ : Fin n → ℝ) :
    ∃ x : ℝ → Fin n → ℝ, IsSolution A I x ∧ x t₀ = x₀ ∧
      ∀ y : ℝ → Fin n → ℝ, IsSolution A I y → y t₀ = x₀ → Set.EqOn y x I := by sorry

end TeschlODE.Linear
