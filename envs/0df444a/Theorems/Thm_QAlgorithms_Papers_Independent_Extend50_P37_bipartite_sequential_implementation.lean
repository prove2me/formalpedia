-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_bipartite_sequential_implementation
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.bipartite_sequential_implementation
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T14:43:52.908314+00:00
-- url     : https://prove2.me/theorems/6c67c764-4417-403f-83b7-3b1e22b463b3
-- title:
--   Remark 18: sequential implementation of the bipartite simulator
-- statement:
--   Let $M_+$ and $M_-$ be normalized locally gauge-symmetric POVMs on two systems. First perform the coherent Lüders sector measurement $\{\Pi_+,\Pi_-\}$, then the corresponding POVM, and report only the second outcome. Its normalized effect measure is
--   $$N(B)=\Pi_+M_+(B)\Pi_++\Pi_-M_-(B)\Pi_-.$$
--   For every density matrix $\rho$, its event probability is the sum of the Born probabilities of $M_\pm(B)$ on the subnormalized states $\Pi_\pm\rho\Pi_\pm$. The sign is used internally.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 31, Remark 18: sequential implementation of the bipartite simulator

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

/-- PDF p.31, Remark 18: Lueders sector measurement followed by the
conditional POVM, reporting only its outcome, has the prescribed effects. -/
theorem bipartite_sequential_implementation [Nonempty I] {O : Type*} [MeasurableSpace O]
    (A : StarSubalgebra ℂ (Mat I))
    (Mplus Mminus : Measurements.OperatorPOVM (Fin 2 → I) O)
    (hp : InAlgebra Mplus.operator (tensorAlg 2 (A : Set (Mat I))))
    (hm : InAlgebra Mminus.operator (tensorAlg 2 (A : Set (Mat I)))) :
    ∃ N : Measurements.OperatorPOVM (Fin 2 → I) O,
      (∀ B, MeasurableSet B → N.operator B =
        permutationSector I 2 false * Mplus.operator B * permutationSector I 2 false +
        permutationSector I 2 true * Mminus.operator B * permutationSector I 2 true) ∧
      ∀ rho, IsDensityMatrix rho → ∀ B, MeasurableSet B →
        effectProb (N.operator B) rho =
          effectProb (Mplus.operator B) (permutationSector I 2 false * rho * permutationSector I 2 false) +
          effectProb (Mminus.operator B) (permutationSector I 2 true * rho * permutationSector I 2 true) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
