-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P23_essentialSelfAdjoint_of_denseRestriction
-- name    : QAlgorithms.Papers.Independent.Frontier30.P23.essentialSelfAdjoint_of_denseRestriction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:37:18.210901+00:00
-- url     : https://prove2.me/theorems/c206469f-f705-4f49-9d5a-2b4285f27c24
-- title:
--   Enlarging the domain of an essentially self-adjoint symmetric operator
-- statement:
--   Let $\mathcal H$ be an arbitrary complex Hilbert space, $D$ a complex linear subspace, and $A:D\to\mathcal H$ a linear symmetric operator. Let $D_1\subseteq D$ be a complex linear subspace dense in the ambient space $\mathcal H$, and put $A_1=A|_{D_1}$. If $A_1$ is essentially self-adjoint, then $A$ is essentially self-adjoint and
--
--   $$
--   \overline A=\overline{A_1}.
--   $$
--
--   Here essential self-adjointness means that the operator is closable and its graph closure is self-adjoint. Equality of the closed operators includes equality of their full domains. Neither the original operator nor the restriction is required to be closed, and no separability assumption is imposed.
--
--   This lemma permits enlargement of a symmetric operator's domain while preserving its self-adjoint closure.
--
--   **Formalization Note** The partial linear map carries $D$ as its domain. Its restriction is constructed with `domRestrict`; the subspace-inclusion hypothesis ensures that its domain is exactly $D_1$. Symmetry is `A.IsFormalAdjoint A`. Closability is stated explicitly to exclude the closure operation's fallback value.
-- source:
--   Analytic extension techniques for unitary representations of Banach-Lie groups, arXiv:1102.0213v1, PDF p. 12, Lemma 4.8

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P23

namespace QAlgorithms.Papers.Independent.Frontier30.P23

/-- Merigon–Neeb, arXiv:1102.0213v1, Lemma 4.8, PDF p. 12.
A symmetric operator extending an essentially self-adjoint restriction on an
ambient-dense complex subspace is essentially self-adjoint, with the same closure.
Essential self-adjointness is written explicitly as closability and self-adjointness
of the graph closure. Equality of partial operators below includes their domains;
the source asserts equality of the closures, not equality of the original operators. -/
theorem essentialSelfAdjoint_of_denseRestriction
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (D1 : Submodule ℂ H)
    (hD1 : D1 ≤ A.domain) (hDense : Dense (D1 : Set H))
    (hSymmetric : A.IsFormalAdjoint A)
    (hRestrictionClosable : (A.domRestrict D1).IsClosable)
    (hRestrictionSelfAdjoint : IsSelfAdjoint (A.domRestrict D1).closure) :
    A.IsClosable ∧ IsSelfAdjoint A.closure ∧
      A.closure = (A.domRestrict D1).closure := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P23
