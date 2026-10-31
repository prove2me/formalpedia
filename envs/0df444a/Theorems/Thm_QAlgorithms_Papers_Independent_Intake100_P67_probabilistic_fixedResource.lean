-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P67_probabilistic_fixedResource
-- name    : QAlgorithms.Papers.Independent.Intake100.P67.probabilistic_fixedResource
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:26:29.776303+00:00
-- url     : https://prove2.me/theorems/39c2f0c8-793f-4562-a16f-21713a520de9
-- title:
--   Fixed-resource optimal faithful success and effects
-- statement:
--   Let $N\ge1$ and fix the shared resource to $|\psi^-\rangle^{\otimes N}$. For each port $i$, let $P_s^{\bar A_i}$ be the projector onto residual spin $s$ of the other $N-1$ Alice qubits, with $2s\equiv N-1\pmod2$ and $0\le s\le(N-1)/2$. Put
--
--   $$\Theta_i=2^{-(N-1)}\sum_s\frac{P_s^{\bar A_i}}{\lambda^+_{s+1/2}},\qquad\Pi_i=P^-_{A_iC}\otimes\Theta_i,$$
--
--   where $\lambda_j^+=(N/2+j+1)/2^N$. These operators and their positive failure remainder form a physical faithful protocol and a feasible success SDP point with $X=I$. They attain
--
--   $$p_{\rm ME}(N)=2^{-N}\sum_s\frac{(2s+1)^2N!}{((N-1)/2-s)!\,((N+3)/2+s)!}.$$
--
--   Every input-independent faithful protocol with this resource has Haar average success probability at most $p_{\rm ME}(N)$.
--
--   The parity restriction makes all factorial arguments nonnegative integers.
-- source:
--   Quantum teleportation scheme by selecting one of multiple output ports, arXiv:0901.2975v2, PDF p. 8, §VI A, Eqs. (48)–(51); Appendix D

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P67

noncomputable section

open scoped Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P67

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Advance50.P49 (spinMultiplicity)

/-- PDF pp.7–8, Eqs.(48)–(51), Appendix D pp.12–13: fixed-resource attaining effects
and the upper bound over all physical faithful protocols with that resource. -/
theorem probabilistic_fixedResource (N : ℕ) (hN : 1 ≤ N) :
    IsProbabilisticPortProtocol (1 : Matrix (Qubits N) (Qubits N) ℂ)
      (fun i => embedTheta i (fixedTheta N i)) ∧
    PortSuccessFeasible N 1 (fixedTheta N) ∧
    portSuccessProbability (1 : Matrix (Qubits N) (Qubits N) ℂ)
      (fun i => embedTheta i (fixedTheta N i)) = fixedSuccess N ∧
    (∀ M : Fin N → Matrix (AC N) (AC N) ℂ,
      IsProbabilisticPortProtocol (1 : Matrix (Qubits N) (Qubits N) ℂ) M →
        portSuccessProbability (1 : Matrix (Qubits N) (Qubits N) ℂ) M ≤ fixedSuccess N) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P67

end
