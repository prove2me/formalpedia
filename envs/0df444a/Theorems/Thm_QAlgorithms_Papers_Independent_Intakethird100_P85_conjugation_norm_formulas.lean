-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P85_conjugation_norm_formulas
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P85.conjugation_norm_formulas
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:18:47.8225+00:00
-- url     : https://prove2.me/theorems/9a2873bb-e97f-4000-8e00-ed332d70a623
-- title:
--   Remark 3: conjugation and squared-norm coefficient formulas
-- statement:
--   Let $a,b,c,d$ be dyadic real numbers, put $\omega=e^{i\pi/4}$, and set $t=a\omega^3+b\omega^2+c\omega+d$. Then
--
--   $$t^\dagger=-c\omega^3-b\omega^2-a\omega+d,$$
--   $$|t|^2=t^\dagger t=(a^2+b^2+c^2+d^2)+(cd+bc+ab-da)\sqrt2.$$
--
--   The equality with $t^\dagger t$ views the real squared norm inside $\mathbb C$. The coefficient formula identifies the dyadic part of the squared norm and underlies the weight identity.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, PDF p. 2, Remark 3: conjugation and squared-norm coefficient formulas

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

/-- Remark 3, equations (2),(3), PDF p.2: conjugation and both squared-norm identities. -/
theorem conjugation_norm_formulas (a : DyadicCoordinates) :
    star (dyadicValue a.val) =
      -(a.val 2 : ℂ) * omega ^ 3 - (a.val 1 : ℂ) * omega ^ 2 -
        (a.val 0 : ℂ) * omega + (a.val 3 : ℂ) ∧
    (Complex.normSq (dyadicValue a.val) : ℂ) =
      star (dyadicValue a.val) * dyadicValue a.val ∧
    Complex.normSq (dyadicValue a.val) =
      coordinateWeight a.val +
        (a.val 2 * a.val 3 + a.val 1 * a.val 2 + a.val 0 * a.val 1 - a.val 3 * a.val 0) *
          Real.sqrt 2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P85

end
