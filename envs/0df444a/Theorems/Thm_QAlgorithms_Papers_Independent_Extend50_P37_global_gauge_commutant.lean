-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_global_gauge_commutant
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.global_gauge_commutant
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:20:44.041569+00:00
-- url     : https://prove2.me/theorems/5d14e269-6721-4deb-b51c-ef400b3427b3
-- title:
--   Corollary 4: global commutant of an algebra gauge group
-- statement:
--   Let $\mathcal A\subseteq\operatorname{End}(\mathbb C^d)$ be a unital adjoint-closed algebra, with $d,n\ge1$, and let $G_{\mathcal A}$ be its unitary commutant. Then, on the full tensor space,
--   $$\operatorname{Comm}(Q(G_{\mathcal A}))=\operatorname{Alg}(\mathcal A^{\otimes n},P(S_n)).$$
--   This characterizes every operator with the collective gauge symmetry.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 7, Corollary 4: global commutant of an algebra gauge group

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

/-- PDF p.7, Corollary 4, (3.5). -/
theorem global_gauge_commutant [Nonempty I] (n : ℕ) (hn : 0 < n)
    (A : StarSubalgebra ℂ (Mat I)) :
    Set.centralizer (collectiveImage n (unitaryCentralizer (A : Set (Mat I)))) =
      alg (tensorAlg n (A : Set (Mat I)) ∪ permutations I n) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
