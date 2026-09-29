-- Prove2me | Theorems.Thm_Rudin_ch09_partials_of_differentiable
-- name    : Rudin.ch09_partials_of_differentiable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:15:33.465986+00:00
-- url     : https://prove2.me/theorems/3c1a98b2-6525-4e81-89f5-b8c7a9316767
-- title:
--   Theorem 9.17 — differentiability gives partial derivatives
-- statement:
--   If $\mathbf{f}$ is differentiable at $\mathbf{x}$ with derivative $A$, then for each $j$ the partial derivative in the direction $\mathbf{e}_j$ exists and equals $A\mathbf{e}_j$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 9, p. 215, Theorem 9.17

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 9.17: if `f` is differentiable at `x` then all partial derivatives exist at
`x` and the derivative applied to the `j`-th basis vector is the `j`-th partial derivative. -/
theorem ch09_partials_of_differentiable (n m : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hf : HasFDerivAt f A x) :
    ∀ j : Fin n,
      HasDerivAt (fun t : ℝ => f (x + t • EuclideanSpace.single j (1 : ℝ)))
        (A (EuclideanSpace.single j (1 : ℝ))) 0 := by sorry

end Rudin
