-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_bipartite_estimation
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.bipartite_estimation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:43:14.780116+00:00
-- url     : https://prove2.me/theorems/cae74241-9b79-401f-91d6-756cbe593ac4
-- title:
--   Theorem 17: bipartite estimation reduces to locally symmetric conditional measurements
-- statement:
--   Let $\mathcal A$ be a unital adjoint-closed algebra on $\mathbb C^d$, $d\ge1$. For a prior on arbitrary bipartite density matrices and a finite measurable parameter vector, assume invariance under both $Q(G_{\mathcal A})$ and swap. Every POVM $M$ admits normalized full-space $\mathcal A\otimes\mathcal A$-valued POVMs $M_+,M_-$ for which
--   $$M'(B)=\Pi_+M_+(B)\Pi_++\Pi_-M_-(B)\Pi_-$$
--   is a normalized POVM with the same positive-probability parameter-conditioned laws as $M$. This is one bipartite input, not identical copies; mixed and entangled inputs are permitted.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 31, Theorem 17: bipartite estimation reduces to locally symmetric conditional measurements

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

/-- PDF p.31, Theorem 17: a single possibly mixed or entangled bipartite
input. Each conditional measurement is normalized on the full space. -/
theorem bipartite_estimation [Nonempty I] {O : Type*} [MeasurableSpace O]
    {l : ℕ} (A : StarSubalgebra ℂ (Mat I)) (p : EstimationPrior (Fin 2 → I) l)
    (hglobal : Symmetry p (collectiveImage 2 (unitaryCentralizer (A : Set (Mat I)))))
    (hswap : Symmetry p (permutations I 2))
    (M : Measurements.OperatorPOVM (Fin 2 → I) O) :
    ∃ Mplus Mminus N : Measurements.OperatorPOVM (Fin 2 → I) O,
      InAlgebra Mplus.operator (tensorAlg 2 (A : Set (Mat I))) ∧
      InAlgebra Mminus.operator (tensorAlg 2 (A : Set (Mat I))) ∧
      (∀ B, MeasurableSet B → N.operator B =
        permutationSector I 2 false * Mplus.operator B * permutationSector I 2 false +
        permutationSector I 2 true * Mminus.operator B * permutationSector I 2 true) ∧
      EquallyInformative p id M.operator N.operator := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
