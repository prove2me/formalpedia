-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_generalized_schur_weyl
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.generalized_schur_weyl
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:18:33.590214+00:00
-- url     : https://prove2.me/theorems/c2a7e887-3208-45fb-bbad-334e9d2c73f8
-- title:
--   Theorem 3: generalization of Schur–Weyl duality (paper seed)
-- statement:
--   Let $G,H\le U(d)$ be mutual unitary centralizers, where $d,n\ge1$. Write $Q(U)=U^{\otimes n}$, $P$ for the ordered permutation representation, and $\operatorname{Alg}$ for the generated complex unital algebra. Then
--   $$\operatorname{Comm}(\operatorname{Alg}Q(G))=\operatorname{Alg}(H^{\times n},P(S_n)),\qquad
--   \operatorname{Comm}(\operatorname{Alg}(H^{\times n},P(S_n)))=\operatorname{Alg}Q(G).$$
--   These mutual commutant identities express the dual reductive pair, equivalently the one-to-one pairing of occurring irreducibles with multiplicity-free joint action.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 7, Theorem 3: generalization of Schur–Weyl duality (paper seed)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P37

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Next46.P29 (phaseAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixBorel

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- PDF p.7, Theorem 3: both full matrix commutant identities. Generated algebra
of local products and permutations, without an unneeded unique factorization. -/
theorem generalized_schur_weyl [Nonempty I] (n : ℕ) (hn : 0 < n)
    (G H : Set (Mat I)) (hG : UnitarySubgroup G) (hH : UnitarySubgroup H)
    (hGH : unitaryCentralizer G = H) (hHG : unitaryCentralizer H = G) :
    Set.centralizer (alg (collectiveImage n G)) = alg (localSet n H ∪ permutations I n) ∧
      Set.centralizer (alg (localSet n H ∪ permutations I n)) = alg (collectiveImage n G) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
