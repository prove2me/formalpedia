-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P19_attenuation_quantum_capacity
-- name    : QAlgorithms.Papers.Independent.Advance50.P19.attenuation_quantum_capacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:55:18.921245+00:00
-- url     : https://prove2.me/theorems/aacf8f2b-ff3a-45d8-863d-72c7d539de31
-- title:
--   One-mode attenuation quantum capacity
-- statement:
--   Let $0\le p\le 1/2$, and let $T_p$ be the one-mode attenuation channel, represented on a qubit by Kraus operators $K_0=|0\rangle\langle0|+\sqrt{1-p}|1\rangle\langle1|$ and $K_1=\sqrt p|0\rangle\langle1|$. Let $Q(T_p)$ denote its ordinary unassisted operational quantum capacity in qubits per use, allowing arbitrary collective CPTP encoders and decoders. Write $H_2(x)=-x\log_2 x-(1-x)\log_2(1-x)$, with $0\log_2 0=0$. Then
--
--   $$Q(T_p)=\max_{-1\le\lambda\le1}\left[H_2\!\left(\frac{(1-p)(1-\lambda)}2\right)-H_2\!\left(\frac{p(1-\lambda)}2\right)\right].$$
--
--   The maximum is attained. This reduces the capacity computation to a scalar optimization; the displayed value is for one mode.
-- source:
--   Degradability of Fermionic Gaussian Channels, arXiv:1604.01954v2, PDF p. 4, Unnumbered capacity formula

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P19

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P19

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, unnumbered capacity formula: ONE attenuation mode, in the
closed degradable interval. The maximum is attained, not merely a supremum. -/
theorem attenuation_quantum_capacity (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    ∃ lambda : ℝ, lambda ∈ Set.Icc (-1) 1 ∧
      quantumCapacity (attenuation p) = capacityObjective p lambda ∧
      ∀ mu ∈ Set.Icc (-1 : ℝ) 1,
        capacityObjective p mu ≤ capacityObjective p lambda := by sorry

end QAlgorithms.Papers.Independent.Advance50.P19

end
