-- Prove2me | Theorems.Thm_Rudin_ch09_invertible_open
-- name    : Rudin.ch09_invertible_open
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:06:13.942885+00:00
-- url     : https://prove2.me/theorems/950f6d18-de77-4ce8-994e-f98113324df3
-- title:
--   Theorem 9.8 — the invertible operators form an open set
-- statement:
--   Let $\Omega$ be the set of invertible linear operators on $\mathbb{R}^n$. If $A \in \Omega$ and $\|B - A\|\,\|A^{-1}\| < 1$ then $B \in \Omega$; consequently $\Omega$ is open in $L(\mathbb{R}^n)$, and the map $A \mapsto A^{-1}$ is continuous on $\Omega$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 9, p. 209, Theorem 9.8

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 9.8: the set `Ω` of invertible linear operators on `ℝⁿ` is open — indeed
`B ∈ Ω` whenever `‖B - A‖ ‖A⁻¹‖ < 1` for some `A ∈ Ω` — and inversion is continuous on `Ω`. -/
theorem ch09_invertible_open (n : ℕ)
    (inv : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hinv : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      Function.Bijective A → (∀ x, inv A (A x) = x) ∧ ∀ y, A (inv A y) = y) :
    (∀ A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
        Function.Bijective A → ‖B - A‖ * ‖inv A‖ < 1 → Function.Bijective B) ∧
    IsOpen {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) | Function.Bijective A} ∧
    ContinuousOn inv {A | Function.Bijective A} := by sorry

end Rudin
