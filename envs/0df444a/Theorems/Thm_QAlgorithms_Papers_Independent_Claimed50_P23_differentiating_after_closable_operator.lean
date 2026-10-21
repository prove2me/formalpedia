-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P23_differentiating_after_closable_operator
-- name    : QAlgorithms.Papers.Independent.Claimed50.P23.differentiating_after_closable_operator
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:10:20.051511+00:00
-- url     : https://prove2.me/theorems/1e46b8ed-625d-440b-9d86-aa9ba3f42f2a
-- title:
--   Differentiation after a closable operator
-- statement:
--   Let $H$ be any complex Hilbert space and $D\subseteq H$ a dense complex linear subspace. Let $A:D\to D$ be complex linear and essentially skew-adjoint as an operator in $H$, and let $B:D\to H$ be a complex linear closable operator. Write $U_A(t)=e^{t\overline A}$ for the strongly continuous unitary group of the graph closure of $A$. Suppose $U_A(t)D\subseteq D$ for every real $t$. If $v\in D$ and $t\mapsto BAU_A(t)v$ is continuous in $H$, then
--
--   $$
--   \frac{d}{dt}BU_A(t)v=BAU_A(t)v\qquad(t\in\mathbb R).
--   $$
--
--   No invariance or skew-symmetry of $B$ is assumed. The result permits differentiation through an unbounded closable operator when the stated graph-domain conditions hold.
-- source:
--   Integrating representations of Banach--Lie algebras, arXiv:1003.0999v3, PDF p. 3, Lemma 5

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P23

noncomputable section

open MeasureTheory

open scoped Interval Classical

namespace QAlgorithms.Papers.Independent.Claimed50.P23

section HilbertStatements

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lemma 5, PDF pp.3--4: differentiation after a merely closable B. Only A
preserves D; B need not map D back to D, be bounded, or be skew-symmetric. -/
theorem differentiating_after_closable_operator
    [CompleteSpace H]
    (D : Submodule ℂ H) (hDense : Dense (D : Set H))
    (A : D →ₗ[ℂ] D) (B : D →ₗ[ℂ] H)
    (hA : EssentiallySkewAdjoint (onDomain D (D.subtype.comp A)))
    (hInvariant : InvariantDomain D (D.subtype.comp A))
    (hB : (onDomain D B).IsClosable) (v : D)
    (hContinuous : Continuous (fun t : ℝ =>
      B (A (operatorOrbit D (D.subtype.comp A) t v)))) :
    ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => B (operatorOrbit D (D.subtype.comp A) s v))
      (B (A (operatorOrbit D (D.subtype.comp A) t v))) t := by sorry

end HilbertStatements

end QAlgorithms.Papers.Independent.Claimed50.P23

end
