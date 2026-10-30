-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_qutrit_no_local_simulator
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.qutrit_no_local_simulator
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:30:04.955994+00:00
-- url     : https://prove2.me/theorems/dfaa2a02-c504-43fe-8fa8-df83f03d5eca
-- title:
--   IV B 3: phase symmetry without the gauge property does not suffice
-- statement:
--   For $N=\operatorname{diag}(0,1,2)$ the scalar-extended phase group on a qutrit is not gauge. Put $v_\pm=(|11\rangle\pm|02\rangle\pm|20\rangle)/\sqrt3$ and
--   $$F_0=\tfrac12|v_+\rangle\langle v_+|,\quad F_1=\tfrac12|v_-\rangle\langle v_-|,\quad F_2=I-F_0-F_1.$$
--   These effects form a globally phase-invariant POVM. No locally phase-invariant three-outcome POVM reproduces its outcome probabilities on every symmetric-supported density matrix. Normalization and scaling make the source’s nonorthogonal vectors into legitimate POVM effects.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 17, IV B 3: phase symmetry without the gauge property does not suffice

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

/-- PDF p.17: the scalar-extended qutrit phase group is not gauge, and the
concrete globally symmetric measurement has no locally symmetric simulator
on all symmetric-sector density matrices. -/
theorem qutrit_no_local_simulator :
    ¬ IsGauge (phaseGroup 3) ∧ IsPOVM qutritEffects ∧
    (∀ j, qutritEffects j ∈ Set.centralizer (collectiveImage 2 (phaseGroup 3))) ∧
    ¬ ∃ N : Fin 3 → Mat (Fin 2 → Fin 3), IsPOVM N ∧
      (∀ j, N j ∈ Set.centralizer (localSet 2 (phaseGroup 3))) ∧
      ∀ rho, IsDensityMatrix rho →
        permutationSector (Fin 3) 2 false * rho * permutationSector (Fin 3) 2 false = rho →
        ∀ j, effectProb (N j) rho = effectProb (qutritEffects j) rho := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
