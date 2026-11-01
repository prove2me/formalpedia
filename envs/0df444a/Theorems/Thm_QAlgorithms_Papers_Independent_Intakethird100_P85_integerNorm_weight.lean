-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P85_integerNorm_weight
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P85.integerNorm_weight
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:08:41.518675+00:00
-- url     : https://prove2.me/theorems/bde45e00-d3b5-4421-849e-f15ae2287d0c
-- title:
--   Lemma 1: integer squared norm equals squared weight
-- statement:
--   Let $u\in\mathbb D[\omega]^d$, with $d\ge0$ and $\mathbb D=\mathbb Z[1/2]$. Write each coordinate uniquely as $u_j=a_j\omega^3+b_j\omega^2+c_j\omega+d_j$, with dyadic real coefficients. Define $\|u\|^2=\sum_j|u_j|^2$ and $\|u\|_{\mathrm{weight}}^2=\sum_j(a_j^2+b_j^2+c_j^2+d_j^2)$. If $\|u\|^2$ is an integer, then
--
--   $$\|u\|_{\mathrm{weight}}^2=\|u\|^2.$$
--
--   The identity relates coefficient weight to the usual complex norm without assuming unit normalization. The empty vector is included.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, PDF p. 2, Lemma 1: integer squared norm equals squared weight

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

/-- Lemma 1, PDF p.2: squared weight equals an integer squared norm.
Vectors are presented in their unique dyadic omega-power coordinates. -/
theorem integerNorm_weight (d : ℕ) (a : Fin d → DyadicCoordinates)
    (integerNorm : ∃ m : ℤ, vectorNormSq (fun i => dyadicValue (a i).val) = (m : ℝ)) :
    (∑ i, coordinateWeight (a i).val) = vectorNormSq (fun i => dyadicValue (a i).val) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P85

end
