-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P67_probabilistic_optimum
-- name    : QAlgorithms.Papers.Independent.Intake100.P67.probabilistic_optimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:27:10.371443+00:00
-- url     : https://prove2.me/theorems/7ef9e106-def1-4ff8-8b0c-faa4b5e285a6
-- title:
--   Fully optimized faithful success probability N/(N+3)
-- statement:
--   Let $N\ge1$ be an integer and use the physical faithful qubit protocol model of §V. Write $P_j$ for Alice's spin-$j$ projector, $g_N(j)$ for its spin multiplicity, and $h_N=6/((N+1)(N+2)(N+3))$. The resource and transformed successful effects are specified by
--
--   $$X=\sum_j\frac{2^Nh_N(2j+1)}{g_N(j)}P_j,\quad O=\sqrt X,\qquad \Theta_i=\sum_s\frac{2^{N+1}h_N(2s+1)}{Ng_{N-1}(s)}P_s^{\bar A_i}.$$
--
--   All spin sums use their legal parity-correct ranges. With physical successful effects $(X^{-1/2}\otimes I)(P^-_{A_iC}\otimes\Theta_i)(X^{-1/2}\otimes I)$ and the positive failure remainder, these data are feasible and faithful, and
--
--   $$p_{\rm opt}(N)=\frac{N}{N+3}.$$
--
--   Every normalized input-independent resource and faithful Alice sub-POVM on $N$ resource qubits have Haar average success probability at most this value.
--
--   This is the attained qubit optimum; no general-$d$ formula is inferred.
-- source:
--   Quantum teleportation scheme by selecting one of multiple output ports, arXiv:0901.2975v2, PDF p. 8, §VI B, Eqs. (52)–(56); Appendix E

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P67

noncomputable section

open scoped Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P67

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Advance50.P49 (spinMultiplicity)

/-- PDF pp.8–9, Eqs.(52)–(56), Appendix E p.13: explicitly attained success N/(N+3)
and an upper bound over every input-independent resource and faithful Alice sub-POVM. -/
theorem probabilistic_optimum (N : ℕ) (hN : 1 ≤ N) :
    PortSuccessFeasible N (probabilisticX N) (optimalTheta N) ∧
    IsProbabilisticPortProtocol (resourceOperator (probabilisticX N)) (probabilisticMeasurement N) ∧
    portSuccessProbability (resourceOperator (probabilisticX N)) (probabilisticMeasurement N) = probabilisticOptimumSuccess N ∧
    (∀ (O : Matrix (Qubits N) (Qubits N) ℂ)
      (M : Fin N → Matrix (AC N) (AC N) ℂ), IsProbabilisticPortProtocol O M →
        portSuccessProbability O M ≤ probabilisticOptimumSuccess N) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P67

end
