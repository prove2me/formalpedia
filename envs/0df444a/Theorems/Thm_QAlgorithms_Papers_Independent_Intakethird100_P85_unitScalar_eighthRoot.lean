-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P85_unitScalar_eighthRoot
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P85.unitScalar_eighthRoot
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:20:16.898882+00:00
-- url     : https://prove2.me/theorems/b8673612-9eb5-4657-9225-783ec90edb4c
-- title:
--   Remark 7: unit-modulus ring scalars are eighth roots
-- statement:
--   Let $z\in\mathbb Z[1/\sqrt2,i]$ and suppose $|z|=1$. With $\omega=e^{i\pi/4}$,
--
--   $$\exists m\in\{0,1,\ldots,7\},\qquad z=\omega^m.$$
--
--   This is the scalar implication explaining the redundant final determinant condition in Corollary 2. It preserves absolute phase and also applies to zero-qubit unitary operators.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, PDF p. 6, Remark 7: unit-modulus ring scalars are eighth roots

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

/-- Remark 7, PDF p.6: unit-modulus ring scalars are exactly eighth-root powers. -/
theorem unitScalar_eighthRoot (z : ℂ) (ring : z ∈ synthesisRing) (unitModulus : ‖z‖ = 1) :
    ∃ m : Fin 8, z = omega ^ m.val := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P85

end
