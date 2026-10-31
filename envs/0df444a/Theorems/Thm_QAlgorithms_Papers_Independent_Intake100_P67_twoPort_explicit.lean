-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P67_twoPort_explicit
-- name    : QAlgorithms.Papers.Independent.Intake100.P67.twoPort_explicit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:29:46.644946+00:00
-- url     : https://prove2.me/theorems/1965a7e1-e94d-49a0-8c90-24ff1359fb47
-- title:
--   Explicit optimal two-port resource and both successful outputs
-- statement:
--   Let $N=2$, $A=A_1A_2$, and $|\psi^\pm\rangle=(|01\rangle\pm|10\rangle)/\sqrt2$. The canonical optimized resource is
--
--   $$|\psi\rangle=\sqrt{1/10}|\psi^-\rangle_A|\psi^-\rangle_B+\sqrt{3/10}(|00\rangle_A|11\rangle_B+|11\rangle_A|00\rangle_B-|\psi^+\rangle_A|\psi^+\rangle_B).$$
--
--   Define $|x^\pm\rangle=(\pm|\psi^+\rangle+\sqrt3|\psi^-\rangle)/2$, $|\eta^-\rangle=\sqrt{2/3}|x^-\rangle|0\rangle+\sqrt{1/3}|00\rangle|1\rangle$ and $|\eta^+\rangle=\sqrt{2/3}|x^+\rangle|1\rangle-\sqrt{1/3}|11\rangle|0\rangle$. The $\eta$ vectors are orthonormal. The successful effects are the projector $\Pi_1=|\eta^-\rangle\langle\eta^-|+|\eta^+\rangle\langle\eta^+|$ and its $A_1\leftrightarrow A_2$ exchange $\Pi_2$, with positive failure remainder. They equal the optimized physical effects and give total success $2/5$.
--
--   For every normalized input $|v\rangle$, the square-root postmeasurement vector in branch 1 is
--
--   $$\sqrt{\Pi_1}(|\psi\rangle|v\rangle_C)=5^{-1/2}|\psi_{\rm res}\rangle_{ACB_2}|v\rangle_{B_1},$$
--
--   where the normalized residual is
--
--   $$|\psi_{\rm res}\rangle=2^{-1/2}(|\eta^-\rangle|1\rangle-|\eta^+\rangle|0\rangle)=2^{-1/2}|\psi^-\rangle_A|\psi^-\rangle_{CB_2}+6^{-1/2}(|00\rangle|11\rangle+|11\rangle|00\rangle-|\psi^+\rangle|\psi^+\rangle).$$
--
--   Branch 2 has the same expression with both $A_1\leftrightarrow A_2$ and $B_1\leftrightarrow B_2$. Each branch has probability $1/5$.
--
--   This pins the physical instrument and its residual state, not only the success probability.
-- source:
--   Quantum teleportation scheme by selecting one of multiple output ports, arXiv:0901.2975v2, PDF p. 9, §VII, Eqs. (57)–(59)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P67

noncomputable section

open scoped Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P67

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Advance50.P49 (spinMultiplicity)

/-- PDF p.9, Eqs.(57)–(59): resource, projective effects, both faithful successful
postmeasurement vectors and their residual Bell expansion. Each branch has probability 1/5. -/
theorem twoPort_explicit :
    (∀ a b, resource (resourceOperator (probabilisticX 2)) a b = twoPortResource a b) ∧
    IsState (twoPortEta false) ∧ IsState (twoPortEta true) ∧ inner ℂ (twoPortEta false) (twoPortEta true) = 0 ∧
    (∀ i : Fin 2, probabilisticMeasurement 2 i = twoPortMeasurement i ∧
      twoPortMeasurement i * twoPortMeasurement i = twoPortMeasurement i) ∧
    IsProbabilisticPortProtocol (resourceOperator (probabilisticX 2)) twoPortMeasurement ∧
    portSuccessProbability (resourceOperator (probabilisticX 2)) twoPortMeasurement = 2 / 5 ∧
    (∀ a c t, twoPortResidual a c t = twoPortResidualExpanded a c t) ∧
    (∑ a : Qubits 2, ∑ c : Bool, ∑ t : Bool,
      Complex.normSq (twoPortResidual a c t)) = 1 ∧
    (∀ (v : EuclideanSpace ℂ Bool), IsState v →
      (∀ a c b,
        postAmplitude (resourceOperator (probabilisticX 2)) (twoPortMeasurement 0) v a c b =
          (Real.sqrt 5 : ℂ)⁻¹ * twoPortResidual a c (b 1) * v (b 0)) ∧
      (∀ a c b,
        postAmplitude (resourceOperator (probabilisticX 2)) (twoPortMeasurement 1) v a c b =
          (Real.sqrt 5 : ℂ)⁻¹ * twoPortResidual (swapTwo a) c (b 0) * v (b 1)) ∧
      (∀ i : Fin 2,
        postBranchProbability (resourceOperator (probabilisticX 2)) (twoPortMeasurement i) v = 1 / 5)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P67

end
