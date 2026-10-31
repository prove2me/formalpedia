-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P37_polarization_covariance
-- name    : QAlgorithms.Papers.Independent.Intake100.P37.polarization_covariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:01:56.469601+00:00
-- url     : https://prove2.me/theorems/6f9fe95b-5f50-46e0-853b-bc868ce80112
-- title:
--   Physical polarization covariance and universality
-- statement:
--   Fix atom count $A\ge0$, input photon count $m\ge0$, and real $\gamma,t$. In the original atomic convention let $R(U)$ act by the bosonic photon representation of $U\in U(2)$ and by $\overline U$ on each ground doublet, fixing $e$. Then $R(U)$ is unitary, commutes with the physical Hamiltonian, and transports both the all-excited input and its full evolution under $\psi\mapsto U\psi$.
--
--   After the fixed relabeling $g_1\mapsto b_2$, $g_2\mapsto-b_1$, let $S(U)$ act fundamentally on both $a$ and $b$, fixing $c$. For $U\in SU(2)$, $S(U)$ is unitary and
--
--   $$
--   [H,R(U)]=0,\qquad [H_{\rm five},S(U)]=0,
--   \qquad R(U)E=ES(U).
--   $$
--
--   Here $E$ is the explicit embedding of singlet-convention oscillator states into the individual-atom sector. For every normalized $\psi$, the specified matrix with columns $\psi$ and $(-\overline{\psi_1},\overline{\psi_0})$ belongs to $SU(2)$. For each $0\le l\le A$, measuring $A-l$ excited atoms has probability $|f_l(t)|^2$, independent of $\psi$, where $f_l$ is the derived transfer-matrix amplitude. This gives the universality used by the physical cloning statements.
-- source:
--   Lambda's, V's and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, PDF p. 2, Sec. II; Eq.(14) on p.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P37

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2 and p.4: active U(2) covariance in the original atomic basis;
in the singlet convention the simultaneous fundamental action is SU(2).
Universality and input-independent sector probabilities are conclusions. -/
theorem polarization_covariance (A m : ℕ) (gamma t : ℝ) :
    (∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
      physicalRotation A m U.val ∈ Matrix.unitaryGroup (LambdaEnergyBasis 2 A m) ℂ ∧
      physicalH 2 A m gamma * physicalRotation A m U.val =
        physicalRotation A m U.val * physicalH 2 A m gamma ∧
      (∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
        physicalInput A m (act U.val psi) =
          act (physicalRotation A m U.val) (physicalInput A m psi) ∧
        physicalOutput A m gamma t (act U.val psi) =
          act (physicalRotation A m U.val) (physicalOutput A m gamma t psi))) ∧
    (∀ U : Matrix.unitaryGroup (Fin 2) ℂ, Matrix.det U.val = 1 →
      fiveRotation A m U.val ∈ Matrix.unitaryGroup (OscBasis 2 A m) ℂ ∧
      fiveH A m gamma * fiveRotation A m U.val =
        fiveRotation A m U.val * fiveH A m gamma ∧
      physicalRotation A m U.val * singletEmbedding A m =
        singletEmbedding A m * fiveRotation A m U.val) ∧
    (∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
      polarizationLift psi ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      Matrix.det (polarizationLift psi) = 1 ∧
      ∀ l : Fin (A + 1), excitedOutcomeProbability A m l.val gamma t psi =
        Complex.normSq (emissionAmplitude A m gamma t l)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P37

end
