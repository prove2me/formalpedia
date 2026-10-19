-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_unital_accessibilityDichotomy
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.unital_accessibilityDichotomy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:36:26.668617+00:00
-- url     : https://prove2.me/theorems/2abe2d96-d3b8-47e2-bc86-fab928578390
-- title:
--   Proposition 5.11: Accessibility dichotomy for unital systems
-- statement:
--   For a unital GKSL generator on $\mathbb C^n$, if $n=2$ then generic direct accessibility is equivalent to the generator not being purely Hamiltonian. If $n>2$, exactly one of these holds:
--
--   $$\text{(R) is generically directly accessible},$$
--
--   or (R) is nowhere directly accessible and every $J(U)$ has identical off-diagonal entries. The common entry may depend on $U$. Generic means open, dense, and full measure; direct accessibility is the real span condition on achievable derivatives.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 26, Proposition 5.11: Accessibility dichotomy for unital systems

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

/-- arXiv:2308.00561v1, PDF p.26, Proposition 5.11: Accessibility dichotomy for unital systems. The rate constant is chosen after U. Xor makes the two alternatives exclusive. The barycenter is not asserted directly accessible. -/
theorem unital_accessibilityDichotomy {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) (hu : unital D) :
    (n = 2 → (genericallyDirectlyAccessible D ↔ ¬purelyHamiltonian D)) ∧
    (2 < n → Xor' (genericallyDirectlyAccessible D)
      (nowhereDirectlyAccessible D ∧ ∀ U, specialUnitary U →
        ∃ c : ℝ, ∀ i j, i ≠ j → rates D.jump U i j = c)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
