-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P67_fixedResource_entanglementConsumption
-- name    : QAlgorithms.Papers.Independent.Intake100.P67.fixedResource_entanglementConsumption
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:32:12.771693+00:00
-- url     : https://prove2.me/theorems/2ebc8078-d4e7-44b0-a6f0-c1fb847eb230
-- title:
--   At least one ebit consumed with a fixed singlet resource
-- statement:
--   Let $N\ge1$ and use the fixed resource $|\psi^-\rangle^{\otimes N}$ and the attaining faithful probabilistic effects (48), with the square-root instrument and all Alice systems retained. For every normalized pure input and each successful port the branch probability is positive, and the normalized residual marginal on the unused Bob ports is a density matrix. If $E_{\rm ini}$ is the initial entanglement across $A:B$ and $E_{\rm res}$ is the pure residual entanglement across all Alice systems versus unused Bob ports, in bits, then
--
--   $$E_{\rm ini}=N,\qquad E_{\rm res}\le N-1,\qquad E_{\rm ini}-E_{\rm res}\ge1.$$
--
--   At $N=1$ the residual Bob register is empty and has zero entropy. The successful output qubit is excluded from the residual.
--
--   The approximate numerical examples on the page are not asserted as exact equalities.
-- source:
--   Quantum teleportation scheme by selecting one of multiple output ports, arXiv:0901.2975v2, PDF p. 10, §VIII

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P67

noncomputable section

open scoped Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P67

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Advance50.P49 (spinMultiplicity)

/-- PDF p.10, §VIII: a fixed maximally entangled resource consumes at least one ebit
on success; the residual contains only N-1 Bob qubits. -/
theorem fixedResource_entanglementConsumption (N : ℕ) (hN : 1 ≤ N)
    (v : EuclideanSpace ℂ Bool) (hv : IsState v) (i : Fin N) :
    vnEntropy (bobDensity (1 : Matrix (Qubits N) (Qubits N) ℂ)) = (N : ℝ) ∧
    0 < postBranchProbability (1 : Matrix (Qubits N) (Qubits N) ℂ)
      (embedTheta i (fixedTheta N i)) v ∧
    IsDensityMatrix (residualDensity (1 : Matrix (Qubits N) (Qubits N) ℂ)
      (embedTheta i (fixedTheta N i)) v i) ∧
    vnEntropy (residualDensity (1 : Matrix (Qubits N) (Qubits N) ℂ)
      (embedTheta i (fixedTheta N i)) v i) ≤ (N : ℝ) - 1 ∧
    1 ≤ vnEntropy (bobDensity (1 : Matrix (Qubits N) (Qubits N) ℂ)) -
      vnEntropy (residualDensity (1 : Matrix (Qubits N) (Qubits N) ℂ)
        (embedTheta i (fixedTheta N i)) v i) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P67

end
