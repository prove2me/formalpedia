-- Prove2me | Theorems.Thm_Rudin_ch09_C1_iff_partials_continuous
-- name    : Rudin.ch09_C1_iff_partials_continuous
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:16:06.008347+00:00
-- url     : https://prove2.me/theorems/084c04f1-7daa-4e3d-8a0b-476f1df6027e
-- title:
--   Theorem 9.21 — $C'$ is equivalent to continuous partial derivatives
-- statement:
--   A mapping $\mathbf{f}$ of an open set $E \subseteq \mathbb{R}^n$ into $\mathbb{R}^m$ is continuously differentiable on $E$ if and only if all its partial derivatives exist on $E$ and are continuous there.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 9, p. 219, Definition 9.20 and Theorem 9.21

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 9.21: `f` is continuously differentiable on an open set `E` if and only if
all its partial derivatives exist on `E` and are continuous there. -/
theorem ch09_C1_iff_partials_continuous (n m : ℕ) (E : Set (EuclideanSpace ℝ (Fin n)))
    (hE : IsOpen E) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) :
    ContDiffOn ℝ 1 f E ↔
      ∃ D : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m),
        (∀ j : Fin n, ∀ x ∈ E,
          HasDerivAt (fun t : ℝ => f (x + t • EuclideanSpace.single j (1 : ℝ))) (D j x) 0) ∧
        (∀ j : Fin n, ContinuousOn (D j) E) := by sorry

end Rudin
