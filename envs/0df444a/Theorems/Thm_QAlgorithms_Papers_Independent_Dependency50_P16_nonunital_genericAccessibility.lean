-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_nonunital_genericAccessibility
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.nonunital_genericAccessibility
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:20:22.996262+00:00
-- url     : https://prove2.me/theorems/d39e0364-895a-4732-8561-801043d2ebfc
-- title:
--   Proposition 3.13: Generic accessibility of non-unital systems
-- statement:
--   Let $G=-L$ be a nonunital GKSL generator on $\mathbb C^n$, $n\ge2$, and let the fixed Hermitian controls generate at least $\mathfrak{su}(n)$ with unrestricted locally integrable real amplitudes. Then
--
--   $$\text{(R) is generically directly accessible, and (B) is generically accessible.}$$
--
--   Generic means on an open dense subset of full measure in the respective state space. Reduced direct accessibility means that the real span of achievable derivatives is the entire zero-sum tangent space.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 13, Proposition 3.13: Generic accessibility of non-unital systems

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

/-- arXiv:2308.00561v1, PDF p.13, Proposition 3.13: Generic accessibility of non-unital systems. Genericity includes all three conditions. Full-state measure uses actual coordinates on the traceless Hermitian tangent space, not ambient complex-matrix Lebesgue measure. -/
theorem nonunital_genericAccessibility {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (C : FullControls n) (h : ¬unital D) :
    genericallyDirectlyAccessible D ∧ genericallyAccessibleB D C := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
