-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_proposition_1_4
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.proposition_1_4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:45:22.869213+00:00
-- url     : https://prove2.me/theorems/849103e3-a016-407e-bb8e-73dedf1dea52
-- title:
--   Proposition 1.4
-- statement:
--   Let $M$ be a finite-dimensional semisimple unital complex algebra and let $N\subseteq M$ be a semisimple unital subalgebra, as in the surrounding semisimple-chain setting. Then
--
--   $$\bigl[\dim_{\mathbb C}\operatorname{Hom}_N(W,\operatorname{Res}_N V)\leq1\text{ for all irreducible }V,W\bigr]\iff Z(M,N)\text{ is commutative}.$$
--
--   Here irreducible modules are nonzero and finite-dimensional, and $Z(M,N)$ consists of elements of $M$ commuting with $N$. This criterion relates actual restriction multiplicities to a concrete subalgebra.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 8, Proposition 1.4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Proposition 1.4 (PDF p.8). Both algebras are finite-dimensional semisimple
complex unital algebras. Semisimplicity of N is inherited from p.7 and used by
complete reducibility in the proof, though not repeated in the proposition. -/
theorem proposition_1_4 {M : Type*} [Ring M] [Algebra ℂ M]
    [FiniteDimensional ℂ M] [IsSemisimpleRing M]
    (N : Subalgebra ℂ M) [IsSemisimpleRing N] :
    HasSimpleRestriction N.val ↔
      IsCommutativeSubalgebra (Subalgebra.centralizer ℂ (N : Set M)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
