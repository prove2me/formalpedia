-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P37_mixingBias_optimal
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P37.mixingBias_optimal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:22:13.540803+00:00
-- url     : https://prove2.me/theorems/1be8492f-e154-40d8-94ed-703c98896d5e
-- title:
--   Observation 1: optimal mixing bias
-- statement:
--   Fix an integer $d\ge1$. For every unitary $U=(u_{ij})$ on $\mathbb C^d$, take $p_1,p_2$ to be exactly the weights in Eq. (11). Then
--
--   $$\frac{p_1}{p_2}\le\sqrt d.$$
--
--   Every unitary with $|u_{ij}|=1/\sqrt d$ for all $i,j$ attains equality, and such a unitary exists in every positive dimension. Thus the upper bound is attained, not merely approached. At $d=1$ the ratio is one and the construction has zero key yield.
-- source:
--   Low dimensional bound entanglement with one-way distillable cryptographic key, arXiv:quant-ph/0506203v1, PDF p. 2, Observation 1: optimal mixing bias

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P37

noncomputable section

open scoped Matrix BigOperators ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P24
  (Key IsPrivate xForm twist twistingMatrix associatedCCQ transposeSecond transposeBob partyCut)

/-- PDF pp.2--3, Observation 1: global upper bound and attainment at flat
unitaries. d=1 is included; its optimal ratio is one and its key yield is zero. -/
theorem mixingBias_optimal (d : ℕ) (hd : 0 < d) :
    (∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      weightOne (U : Op (Fin d)) / weightTwo (U : Op (Fin d)) ≤ Real.sqrt d) ∧
    (∀ U : Matrix.unitaryGroup (Fin d) ℂ, IsFlatUnitary (U : Op (Fin d)) →
      weightOne (U : Op (Fin d)) / weightTwo (U : Op (Fin d)) = Real.sqrt d) ∧
    (∃ U : Matrix.unitaryGroup (Fin d) ℂ, IsFlatUnitary (U : Op (Fin d)) ∧
      weightOne (U : Op (Fin d)) / weightTwo (U : Op (Fin d)) = Real.sqrt d) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P37

end
