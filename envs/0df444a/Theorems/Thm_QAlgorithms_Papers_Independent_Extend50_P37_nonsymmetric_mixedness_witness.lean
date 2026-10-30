-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_nonsymmetric_mixedness_witness
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.nonsymmetric_mixedness_witness
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:39:46.426033+00:00
-- url     : https://prove2.me/theorems/62de5ba6-b597-48dc-9d6a-4fbe5fb5f3e8
-- title:
--   V B 2: nonsymmetric outcome witnesses mixedness
-- statement:
--   For $n\ge2$ and a density matrix $\rho$ on a nonzero finite-dimensional complex Hilbert space,
--   $$\operatorname{tr}((I-\Pi_+)\rho^{\otimes n})=0\quad\text{if }\rho\text{ is pure},\qquad
--   \operatorname{tr}((I-\Pi_+)\rho^{\otimes n})>0\quad\text{if }\rho\text{ is mixed}.$$
--   A nonsymmetric-sector outcome therefore unambiguously excludes the pure branch. The copy threshold is necessary: for one copy $\Pi_+=I$. This witness alone does not compare all entangled and unentangled strategies.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 24, V B 2: nonsymmetric outcome witnesses mixedness

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

/-- PDF p.24: a nonsymmetric outcome has zero probability for pure iid
states and strictly positive probability for a genuinely mixed iid state.
The printed unqualified claim needs n>=2; n=1 has Pi_plus=I. -/
theorem nonsymmetric_mixedness_witness [Nonempty I] (n : ℕ) (hn : 2 ≤ n) :
    (∀ rho : Mat I, IsDensityMatrix rho → RankOne rho →
      effectProb (1 - permutationSector I n false) (piKron n rho) = 0) ∧
    (∀ rho : Mat I, IsDensityMatrix rho → ¬ RankOne rho →
      0 < effectProb (1 - permutationSector I n false) (piKron n rho)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
