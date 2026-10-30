-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_mixed_reduction_failure
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.mixed_reduction_failure
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T14:35:55.351443+00:00
-- url     : https://prove2.me/theorems/d131ab1e-acd1-4a46-bc22-e5c2c7b3d835
-- title:
--   V A: the reduction equivalence fails for mixed states
-- statement:
--   On a qubit, $g(\rho)=\operatorname{tr}(\rho^2)$ is invariant under every unitary conjugation. Yet the pure state $\rho=|0\rangle\langle0|$ and the mixed state $\sigma=I/2$ have identical reductions to $\mathbb C I$ and satisfy
--   $$g(\rho)=1,\qquad g(\sigma)=\tfrac12.$$
--   Thus gauge invariance does not imply dependence only on the algebra reduction for mixed-state domains.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 22, V A: the reduction equivalence fails for mixed states

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

/-- PDF p.22: purity is unitary invariant but not determined by the scalar
algebra reduction; a nontrivial dimension is required for the witness. -/
theorem mixed_reduction_failure :
    (∀ rho : Mat (Fin 2), IsDensityMatrix rho →
      ∀ U ∈ unitaryCentralizer ({1} : Set (Mat (Fin 2))),
        ((U * rho * Uᴴ) ^ 2).trace.re = (rho ^ 2).trace.re) ∧
    let rho : Mat (Fin 2) := Matrix.diagonal ![(1 : ℂ),0]
    let sigma : Mat (Fin 2) := (1/2 : ℂ) • 1
    IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
      SameReduction (alg ({1} : Set (Mat (Fin 2)))) rho sigma ∧
      (rho ^ 2).trace.re = 1 ∧ (sigma ^ 2).trace.re = 1/2 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
