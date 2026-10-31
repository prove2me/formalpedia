-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P23_oneDegreeWeyl_uniqueness
-- name    : QAlgorithms.Papers.Independent.Intake100.P23.oneDegreeWeyl_uniqueness
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:38:26.872442+00:00
-- url     : https://prove2.me/theorems/87859a16-8b8b-46d4-84c7-41668f0ed16e
-- title:
--   Uniqueness of the irreducible one-degree Weyl representation
-- statement:
--   Let $H_1,H_2$ be nonzero complex Hilbert spaces and let $W_j:\mathbb R^2\to\mathcal U(H_j)$ be regular irreducible Weyl representations for
--   $$\omega((\eta,q),(\eta',q'))=\eta q'-\eta' q.$$
--   Here the Weyl relation is $W_j(y)W_j(z)=e^{-i\omega(y,z)/2}W_j(y+z)$; regularity means strong continuity of $t\mapsto W_j(ty)$, and irreducibility excludes nontrivial closed invariant subspaces. Then a unitary $U:H_1\to H_2$ exists with
--   $$UW_1(y)=W_2(y)U\qquad(y\in\mathbb R^2).$$
--   This is the one-degree Stone–von Neumann uniqueness assertion. **Formalization Note** The statement uses the regular exponentiated Weyl representation associated with the self-adjoint pair; the coordinate groups determine the generators and their domains through Stone's correspondence.
-- source:
--   Introduction to representations of the canonical commutation and anticommutation relations, arXiv:math-ph/0511030v2, PDF p. 1, Introduction, unnumbered: uniqueness of the irreducible one-degree-of-freedom Weyl pair

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P23

open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.1, Introduction: the one-degree irreducible Weyl-pair uniqueness.
Strongly continuous exponentiated operators encode the self-adjoint generators
through Stone's correspondence; equivalence also intertwines those generators. -/
theorem oneDegreeWeyl_uniqueness
    {H2 : Type*} [NormedAddCommGroup H2] [InnerProductSpace ℂ H2] [CompleteSpace H2]
    [Nontrivial H] [Nontrivial H2]
    (W1 : (ℝ × ℝ) → H →L[ℂ] H) (W2 : (ℝ × ℝ) → H2 →L[ℂ] H2)
    (h1 : IsCCR canonicalPlane W1) (h2 : IsCCR canonicalPlane W2)
    (hr1 : WeylRegular W1) (hr2 : WeylRegular W2)
    (hi1 : HilbertIrreducible W1) (hi2 : HilbertIrreducible W2) :
    EquivalentCCR W1 W2 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P23

end
