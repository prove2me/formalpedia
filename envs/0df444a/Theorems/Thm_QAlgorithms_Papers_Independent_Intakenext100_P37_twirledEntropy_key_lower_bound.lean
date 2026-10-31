-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P37_twirledEntropy_key_lower_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P37.twirledEntropy_key_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:27:31.729994+00:00
-- url     : https://prove2.me/theorems/cc19d50a-a95f-4f21-810a-9a8d02c05523
-- title:
--   Unnumbered experimentally estimable lower bound, Eq.18
-- statement:
--   Let $|\psi\rangle_{ABE}$ be a unit vector before measurement, where $A,B$ are qubits and $E$ is any positive finite-dimensional register. Let $\sigma_{AB}$ be its reduced density matrix, let $\sigma^{\rm ccq}_{ABE}$ be its computational measurement on $A,B$, and let $\mathcal T$ be pinching in the four standard Bell projectors. Write $I_Z(\sigma)$ for the mutual information of the computational outcomes of the untwirled $\sigma$. Then
--
--   $$K_{\to}(\sigma^{\rm ccq}_{ABE})\ge I_Z(\sigma_{AB})-S(\mathcal T(\sigma_{AB})).$$
--
--   For any physical density matrix $\rho_{ABA'B'}$ with positive finite shields, and any computational-key-controlled joint-shield unitary $U_\tau$, put $\sigma=\operatorname{Tr}_{A'B'}(U_\tau\rho U_\tau^\dagger)$ and $L=I_Z(\sigma)-S(\mathcal T(\sigma))$. Measuring the original key qubits and using one forward protocol sequence, chosen before every purifying Eve, achieves $\max(0,L)$, and $K_D(\rho)\ge L$. This transfer uses a pessimistic Eve extension in the analysis. No nonlocal twisting is performed by the honest parties, and the original computational law is not equated to that of the Bell-pinched state.
-- source:
--   Low dimensional bound entanglement with one-way distillable cryptographic key, arXiv:quant-ph/0506203v1, PDF p. 3, Unnumbered experimentally estimable lower bound, Eq.18

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P37

noncomputable section

open scoped Matrix BigOperators ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P24
  (Key IsPrivate xForm twist twistingMatrix associatedCCQ transposeSecond transposeBob partyCut)

/-- PDF pp.3--4, Eq.(18): measured, untwirled mutual information minus the
Bell-pinched entropy. Purity is required BEFORE measurement. The second clause
transfers the estimate to the physical premeasurement resource via privacy
squeezing; the controlled joint-shield unitary is never implemented as LOCC. -/
theorem twirledEntropy_key_lower_bound :
    (∀ e : ℕ, 0 < e → ∀ psi : EuclideanSpace ℂ (Fin 2 × (Fin 2 × Fin e)),
      ‖psi‖ = 1 →
      twirledExpression (Dependency50.P21.marginalAB (pureDensity psi)) ≤
        Frontier30.P12.quantumKeyCapacity (dephaseAB (pureDensity psi))) ∧
    (∀ a b : ℕ, 0 < a → 0 < b → ∀ rho : Op (Key 2 × (Fin a × Fin b)), IsDensityMatrix rho →
      ∀ U : Key 2 → Matrix.unitaryGroup (Fin a × Fin b) ℂ,
        HasMeasuredOneWayRate rho (max 0 (twirledExpression (traceRight (twist U rho)))) ∧
        ENNReal.ofReal (twirledExpression (traceRight (twist U rho))) ≤
          Gap48.P42.distillableKey (physicalFin rho)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P37

end
