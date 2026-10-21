-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P28_proposition_2_7
-- name    : QAlgorithms.Papers.Independent.Renew46.P28.proposition_2_7
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T02:59:09.238119+00:00
-- url     : https://prove2.me/theorems/7b14c227-fb4f-4c07-bb54-917f572aa8df
-- title:
--   Finite-dimensional tensor factors preserve continuous inverse algebras
-- statement:
--   Let $\mathbb K$ be a Hausdorff nondiscrete topological field, $A$ a continuous inverse $\mathbb K$-algebra and $F$ a finite-dimensional associative unital $\mathbb K$-algebra. For a basis $e=(e_1,\ldots,e_n)$ of $F$, transport the product topology on $A^n$ by
--
--   $$
--   \phi_e:A^n\longrightarrow F\otimes_{\mathbb K}A,
--   \qquad (a_i)\longmapsto\sum_{i=1}^n e_i\otimes a_i.
--   $$
--
--   The resulting topology is independent of the basis, and makes $F\otimes_{\mathbb K}A$ a continuous inverse $\mathbb K$-algebra. This is the finite-dimensional tensor construction for continuous inverse algebras; neither $F$ nor $A$ is required to be commutative.
-- source:
--   Lie groups over non-discrete topological fields, arXiv:math/0408008v1, PDF p. 18, Proposition 2.7

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28

namespace QAlgorithms.Papers.Independent.Renew46.P28

open Set

open scoped TensorProduct

universe u v w

/-- Proposition 2.7, PDF pp.18–19: tensoring a CIA with a finite-dimensional
unital associative algebra gives a CIA, and the transported topology is independent
of the chosen basis. Neither algebra is required to be commutative. -/
theorem proposition_2_7
    (K : Type u) [Field K] [TopologicalSpace K] [T2Space K]
    [IsTopologicalDivisionRing K] (hK : ¬ DiscreteTopology K)
    (A : Type v) [Ring A] [Algebra K A] [TopologicalSpace A]
    (hA : continuousInverseAlgebra K A)
    (F : Type w) [Ring F] [Algebra K F] [FiniteDimensional K F]
    (n : ℕ) (b : Module.Basis (Fin n) K F) :
    (∀ (m : ℕ) (c : Module.Basis (Fin m) K F),
      finiteTensorAlgebraTopology K A b = finiteTensorAlgebraTopology K A c) ∧
    (letI : TopologicalSpace (F ⊗[K] A) := finiteTensorAlgebraTopology K A b
     continuousInverseAlgebra K (F ⊗[K] A)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P28
