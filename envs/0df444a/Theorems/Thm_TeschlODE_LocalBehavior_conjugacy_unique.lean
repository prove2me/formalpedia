-- Prove2me | Theorems.Thm_TeschlODE_LocalBehavior_conjugacy_unique
-- name    : TeschlODE.LocalBehavior.conjugacy_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T17:37:49.736218+00:00
-- url     : https://prove2.me/theorems/fea75838-aa73-4243-b808-65fbf144616c
-- title:
--   Corollary 9.8 — uniqueness of the conjugacy ϕ = id + bounded with ϕ ∘ A = f ∘ ϕ
-- statement:
--   Let $A$ be an invertible real $n \times n$ matrix with no eigenvalue on the unit circle, and let $f : \mathbb{R}^n \to \mathbb{R}^n$ be arbitrary. If $\phi_1, \phi_2$ are homeomorphisms of $\mathbb{R}^n$ of the form $\phi_i(x) = x + h_i(x)$ with $h_i$ bounded and
--   $$\phi_i \circ A = f \circ \phi_i, \qquad (9.33)$$
--   then $\phi_1 = \phi_2$.
--
--   In the proof of the Hartman–Grobman theorem this uniqueness is what upgrades a conjugacy for the time-one map to a conjugacy for all times.
--
--   **Formalization Note.** "Let $A$ be as in the previous lemma" is read as: invertible with no eigenvalue on the unit circle; the adapted norm of Lemma 9.7 plays no role, since boundedness does not depend on the norm. Uniqueness is stated as "any two such homeomorphisms are equal"; $f$ is an arbitrary function with no regularity.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 264, Corollary 9.8

import Mathlib
import Definitions.Def_TeschlODE_LocalBehavior_eigenvalues

namespace TeschlODE.LocalBehavior

/-- Teschl, Corollary 9.8, p. 264: let `A` be an invertible real matrix with no eigenvalue on the
unit circle (as in Lemma 9.7) and `f : ℝⁿ → ℝⁿ` arbitrary. A homeomorphism `ϕ = id + h` with `h`
bounded and `ϕ ∘ A = f ∘ ϕ` (9.33) is unique: any two such homeomorphisms coincide. -/
theorem conjugacy_unique {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hAinv : IsUnit A)
    (hA : ∀ z ∈ eigenvalues A, ‖z‖ ≠ 1) (f : (Fin n → ℝ) → (Fin n → ℝ))
    (ϕ₁ ϕ₂ : (Fin n → ℝ) ≃ₜ (Fin n → ℝ))
    (hb₁ : ∃ C : ℝ, ∀ x, ‖ϕ₁ x - x‖ ≤ C) (hb₂ : ∃ C : ℝ, ∀ x, ‖ϕ₂ x - x‖ ≤ C)
    (hc₁ : ∀ x, ϕ₁ (A.mulVec x) = f (ϕ₁ x)) (hc₂ : ∀ x, ϕ₂ (A.mulVec x) = f (ϕ₂ x)) :
    ϕ₁ = ϕ₂ := by sorry

end TeschlODE.LocalBehavior
