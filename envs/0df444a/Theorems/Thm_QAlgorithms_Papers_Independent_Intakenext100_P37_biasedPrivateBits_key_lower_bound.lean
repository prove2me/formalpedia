-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P37_biasedPrivateBits_key_lower_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P37.biasedPrivateBits_key_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:20:28.81731+00:00
-- url     : https://prove2.me/theorems/9ffbf313-186d-4869-8f54-86897738716e
-- title:
--   Proposition 1: biased mixture of two private bits
-- statement:
--   Let $A,B$ be key qubits and $A',B'$ be shields of arbitrary positive finite dimensions. Let $\gamma_1,\gamma_2$ be private bits on these same registers in the same computational key basis, with arbitrary mixed shield states. Suppose $p_1,p_2\ge0$, $p_1+p_2=1$, and $p_1>p_2$. Define $\rho=p_1\gamma_1+p_2 X_A\gamma_2X_A$, where $X_A$ flips only Alice's key qubit. Then
--
--   $$K_D(\rho)\ge1-h(p_1).$$
--
--   More specifically, computational measurement of $A,B$ followed by forward authenticated public discussion achieves this rate on independent copies, with one protocol sequence valid for every purifying Eve and with its transcript included in Eve's output. No extra orthogonality hypothesis on the two unflipped private bits is imposed; the flip creates the even/odd key supports. The endpoint $p_2=0$ is permitted. This gives an achievable rate, not an equality with the optimal key rate.
-- source:
--   Low dimensional bound entanglement with one-way distillable cryptographic key, arXiv:quant-ph/0506203v1, PDF p. 1, Proposition 1: biased mixture of two private bits

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P37

noncomputable section

open scoped Matrix BigOperators ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P24
  (Key IsPrivate xForm twist twistingMatrix associatedCCQ transposeSecond transposeBob partyCut)

/-- PDF pp.1--2, Proposition 1 and its final one-way-protocol paragraph.
The second private bit is flipped on Alice's key, yielding the required odd support.
The endpoints p2=0 and p1=1 are allowed. -/
theorem biasedPrivateBits_key_lower_bound {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (gamma1 gamma2 : Op (Key 2 × (Fin a × Fin b))) (hgamma1 : IsPrivate gamma1)
    (hgamma2 : IsPrivate gamma2) (p1 p2 : ℝ) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2)
    (hsum : p1 + p2 = 1) (hbias : p2 < p1) :
    HasMeasuredOneWayRate (privateMixture p1 p2 gamma1 gamma2) (1-binEntropy2 p1) ∧
    ENNReal.ofReal (1-binEntropy2 p1) ≤
      Gap48.P42.distillableKey (physicalFin (privateMixture p1 p2 gamma1 gamma2)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P37

end
