-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P38_cstarTrace
-- name    : QAlgorithms.Papers.Independent.Renew46.P38.cstarTrace
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:09:10.509499+00:00
-- url     : https://prove2.me/theorems/bf286f35-0441-4bd7-ab7b-10636d5435d5
-- title:
--   Jensen’s trace inequality for C*-algebras
-- statement:
--   Let $I$ be a real interval and $f:I\to\mathbb R$ continuous and convex. Let $A$ be a complex C*-algebra. For every positive integer $n$, self-adjoint $x_i\in A$ with spectra in $I$, and $a_i\in A$ satisfying $\sum_i a_i^*a_i=1$, each finite positive tracial functional $\tau$ satisfies
--   $$\tau\!\left(f\!\left(\sum_i a_i^*x_i a_i\right)\right)\leq\tau\!\left(\sum_i a_i^*f(x_i)a_i\right).$$
--   If instead $\tau:A_+\to[0,+\infty]$ is a lower-semicontinuous densely defined trace weight, the same inequality holds provided $f(s)\geq0$ for every $s\in I$. Neither trace is required to be faithful or normalized.
--
--   The entries $a_i$ belong to $A$ itself. Their finite identity decomposition forces admissible $A$ to be unital, which is how it is represented formally. On a unital algebra such a densely defined lower-semicontinuous trace is finite; hence the printed genuinely unbounded corner has no admissible finite-column inputs. The formal weight interface nevertheless retains the extended codomain and nonnegativity clause.
-- source:
--   Jensen's Operator Inequality, arXiv:math/0204049v1, PDF p. 4, Theorem 2.7 (Jensen’s Trace Inequality for C*-Algebras)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P38

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Renew46.P38

universe u

/-- Hansen--Pedersen, Theorem 2.7, PDF p. 4 (proof p. 11).
Both finite traces and lower-semicontinuous densely defined trace weights are retained.
Here a_i belong to A, not M(A). A finite column with sum a_i*a_i=1 already
forces A to contain its identity, so only unital C*-algebras have admissible data.
On a unital algebra the densely defined lower-semicontinuous trace is finite;
there are no genuinely unbounded admissible instances of the printed finite-column clause. -/
theorem cstarTrace (I : Set ℝ) (f : ℝ → ℝ)
    (hI : Set.OrdConnected I) (hf : ContinuousOn f I) (hconv : ConvexOn ℝ I f)
    (A : Type u) [CStarAlgebra A] :
    (∀ (tau : FiniteTrace A) (n : ℕ), 1 ≤ n →
      ∀ x a : Fin n → A, (∀ i, InInterval I (x i)) → columnSquares a = 1 →
        (tau.value (cfc f (combination a x))).re ≤
          (tau.value (combination a (fun i => cfc f (x i)))).re) ∧
    ((∀ s ∈ I, 0 ≤ f s) → ∀ (tau : TraceWeight A) (n : ℕ), 1 ≤ n →
      ∀ x a : Fin n → A, (∀ i, InInterval I (x i)) → columnSquares a = 1 →
        tau.value (cfc f (combination a x)) ≤
          tau.value (combination a (fun i => cfc f (x i)))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P38

end
