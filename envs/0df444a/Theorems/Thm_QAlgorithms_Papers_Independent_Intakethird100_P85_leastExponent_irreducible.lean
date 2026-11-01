-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P85_leastExponent_irreducible
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P85.leastExponent_irreducible
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:10:45.184577+00:00
-- url     : https://prove2.me/theorems/2c249329-92c2-4a76-ba08-46068ebee6c8
-- title:
--   Corollary 1: least exponent and irreducible k-residue
-- statement:
--   Let $t\in\mathbb D[\omega]$, and let $k>0$ be a natural denominator exponent: $(\sqrt2)^k t\in\mathbb Z[\omega]$. Write $\rho_k(t)=\rho((\sqrt2)^k t)$. Then
--
--   $$k\text{ is the least natural denominator exponent of }t
--   \iff\rho_k(t)\text{ is irreducible}.$$
--
--   Here irreducible means not an image of multiplication by the residue of $\sqrt2$. This criterion distinguishes a valid exponent from the least one, including the behavior at $t=0$.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, PDF p. 3, Corollary 1: least exponent and irreducible k-residue

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

/-- Corollary 1, PDF p.3: positive valid k is least iff its residue is irreducible. -/
theorem leastExponent_irreducible (t : ℂ) (ring : InDomega t) (k : ℕ)
    (positive : 0 < k) (valid : ScalarExponent t k) :
    LeastScalarExponent t k ↔ ¬ Reducible (kResidue t k) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P85

end
