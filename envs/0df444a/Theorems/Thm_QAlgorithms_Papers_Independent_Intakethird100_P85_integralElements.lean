-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P85_integralElements
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P85.integralElements
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:18:13.807844+00:00
-- url     : https://prove2.me/theorems/34049425-bb28-45dc-96f6-e5611cabba52
-- title:
--   Remark 2: integral elements of D[omega]
-- statement:
--   Let $z\in\mathbb C$ and $\omega=e^{i\pi/4}$. Then
--
--   $$z\in\mathbb Z[\omega]\iff z\in\mathbb D[\omega]\ \text{and}\ z\text{ is integral over }\mathbb Z.$$
--
--   Integral means a root of a monic polynomial with integer coefficients. The condition $z\in\mathbb D[\omega]$ is retained on the right. This gives the intrinsic characterization of the cyclotomic integer subring.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, PDF p. 2, Remark 2: integral elements of D[omega]

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P85

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P85

open scoped Classical BigOperators

open QAlgorithms

open QAlgorithms.Papers.Independent.Gap48.P10
  (InZomega InDomega Residue bits residue residueMultiply Reducible)

open QAlgorithms.Papers.Independent.Support21.P13
  (synthesisRing integralRing coordinateValue HTLetter htWordMatrix EntriesInRing cliffordTLibrary)

local notation "omega" => QAlgorithms.gateT true true

local notation "sqrtTwo" => ((Real.sqrt 2 : ℝ) : ℂ)

/-- Remark 2, PDF p.2: Z[omega] consists precisely of the algebraic integers in D[omega]. -/
theorem integralElements (z : ℂ) :
    InZomega z ↔ InDomega z ∧ IsIntegral ℤ z := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P85

end
