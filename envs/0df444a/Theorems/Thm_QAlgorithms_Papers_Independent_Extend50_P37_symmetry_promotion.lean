-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_symmetry_promotion
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.symmetry_promotion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:24:44.130671+00:00
-- url     : https://prove2.me/theorems/8b77af4e-cd67-4fe4-8bcb-ec1f87f6ddb8
-- title:
--   Theorem 8: a unital completely positive symmetry-promotion map
-- statement:
--   For every unital adjoint-closed algebra $\mathcal A$, $d,n\ge1$, and each sign, the corrected canonical map $L_\pm$ is complex-linear, unital and completely positive, and
--   $$\operatorname{im}L_\pm\subseteq\mathcal A^{\otimes n}\cap\operatorname{Comm}(P(S_n)).$$
--   For every matrix $M$ whose compression commutes with $Q(G_{\mathcal A})$,
--   $$\Pi_\pm L_\pm(M)\Pi_\pm=\Pi_\pm M\Pi_\pm.$$
--   Here $T$ is the Hilbert–Schmidt conditional expectation onto $\mathcal A^{\otimes n}$, $C=T(\Pi_\pm)$, $R=C^{-1/2}$ on its positive spectral support and zero on its kernel, $\Phi(M)=RT(\Pi_\pm M\Pi_\pm)R$, and $L_\pm(M)=\Phi(M)+\operatorname{tr}(M)(I-\Phi(I))/d^n$. This is the source construction with eigenvalue normalization restored. It is a Heisenberg map and need not preserve trace.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 10, Theorem 8: a unital completely positive symmetry-promotion map

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

/-- PDF pp.10-11, Theorem 8, with the normalized-eigenvalue correction from
(A10), PDF p.35. The canonical map is Heisenberg unital CP. -/
theorem symmetry_promotion [Nonempty I] (n : ℕ) (hn : 0 < n) (s : Bool)
    (A : StarSubalgebra ℂ (Mat I)) :
    Promotes (A : Set (Mat I)) n s (promotion (A : Set (Mat I)) n s) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
