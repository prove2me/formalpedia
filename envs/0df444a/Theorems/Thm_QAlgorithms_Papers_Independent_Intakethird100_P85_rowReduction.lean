-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P85_rowReduction
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P85.rowReduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:11:24.10399+00:00
-- url     : https://prove2.me/theorems/f55445db-278f-4a59-8c79-11377fd7fac2
-- title:
--   Lemma 4 (Row operation): reduce a matched pair
-- statement:
--   Let $u=(u_1,u_2)^T\in\mathbb D[\omega]^2$, and let $k>0$ be a denominator exponent for both entries. Set $x_j=\rho_k(u_j)$ and suppose $x_1^\dagger x_1=x_2^\dagger x_2$ in the residue algebra. There is a finite word $W$ over $H,T$ such that
--
--   $$v=Wu,\qquad (\sqrt2)^{k-1}v\in\mathbb Z[\omega]^2.$$
--
--   The word may be empty, and neither the initial nor the resulting exponent is required to be least. This is the matched-pair operation used to reduce columns.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, PDF p. 4, Lemma 4 (Row operation): reduce a matched pair

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

/-- Lemma 4, PDF p.4: matched residues admit an H/T row word lowering a valid exponent. -/
theorem rowReduction (u : Bool → ℂ) (ring : ∀ b, InDomega (u b)) (k : ℕ)
    (positive : 0 < k) (valid : VectorExponent u k)
    (matched : residueNorm (kResidue (u false) k) = residueNorm (kResidue (u true) k)) :
    ∃ w : List HTLetter, VectorExponent ((htWordMatrix w).mulVec u) (k - 1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P85

end
