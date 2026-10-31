-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P67_optimizedResources_portMarginals
-- name    : QAlgorithms.Papers.Independent.Intake100.P67.optimizedResources_portMarginals
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:29:11.361311+00:00
-- url     : https://prove2.me/theorems/c3173611-787b-4915-92f8-995f7c12511e
-- title:
--   Both optimized resources have maximally mixed individual ports
-- statement:
--   For each integer $N\ge1$, let $|\psi_{\rm det}\rangle$ and $|\psi_{\rm prob}\rangle$ be the explicitly optimized pure resources specified by (34) and (54), using $O=\sqrt X$. Every individual Bob port is maximally mixed:
--
--   $$\operatorname{tr}_{A\bar B_i}|\psi_{\rm det}\rangle\langle\psi_{\rm det}|=\operatorname{tr}_{A\bar B_i}|\psi_{\rm prob}\rangle\langle\psi_{\rm prob}|=\frac{I_{B_i}}2.$$
--
--   For $N\ge2$, the full Bob marginal of each resource differs from $I_B/2^N$, so neither pure resource is maximally entangled across the whole $A:B$ cut.
--
--   The individual-port cut is $B_i$ against all Alice qubits and all other Bob ports together; no claim is made that $B_i$ is maximally entangled with one particular $A_i$.
-- source:
--   Quantum teleportation scheme by selecting one of multiple output ports, arXiv:0901.2975v2, PDF p. 9, §VI B; Eqs. (34),(54)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P67

noncomputable section

open scoped Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P67

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Advance50.P49 (spinMultiplicity)

/-- PDF pp.6,8–9: both optimized resources have maximally mixed single-port marginals.
For N>=2 neither resource is maximally entangled in the whole A:B cut. -/
theorem optimizedResources_portMarginals (N : ℕ) (hN : 1 ≤ N) :
    (∀ i : Fin N,
      bobPortDensity (resourceOperator (deterministicX N)) i =
        (1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ) ∧
      bobPortDensity (resourceOperator (probabilisticX N)) i =
        (1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ)) ∧
    (2 ≤ N →
      bobDensity (resourceOperator (deterministicX N)) ≠
        ((2 : ℂ) ^ N)⁻¹ • (1 : Matrix (Qubits N) (Qubits N) ℂ) ∧
      bobDensity (resourceOperator (probabilisticX N)) ≠
        ((2 : ℂ) ^ N)⁻¹ • (1 : Matrix (Qubits N) (Qubits N) ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P67

end
