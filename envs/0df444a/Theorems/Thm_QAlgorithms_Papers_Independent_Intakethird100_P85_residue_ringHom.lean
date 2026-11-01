-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P85_residue_ringHom
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P85.residue_ringHom
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:19:38.768942+00:00
-- url     : https://prove2.me/theorems/9360140a-d9c9-4429-aabe-25c59e260552
-- title:
--   Remark 5: the residue map is a surjective ring homomorphism
-- statement:
--   Let $\rho:\mathbb Z[\omega]\to\mathbb Z_2[\omega]$ reduce the four omega-power coefficients modulo $2$. The target multiplication is reduction modulo $\omega^4+1$. For cyclotomic integers $s,t$,
--
--   $$\rho(0)=0,\quad\rho(1)=1,\quad\rho(s+t)=\rho(s)+\rho(t),\quad
--   \rho(st)=\rho(s)\rho(t).$$
--
--   Every residue has a preimage in $\mathbb Z[\omega]$. Thus the coefficient residue map is a surjective ring homomorphism. This justifies residue arithmetic in denominator reduction.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, PDF p. 2, Remark 5: the residue map is a surjective ring homomorphism

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

/-- Remark 5, PDF p.2: rho is a surjective ring homomorphism with quotient multiplication. -/
theorem residue_ringHom :
    residue 0 = bits 0 ∧ residue 1 = bits 1 ∧
    (∀ t s : ℂ, InZomega t → InZomega s → residue (t + s) = residue t + residue s) ∧
    (∀ t s : ℂ, InZomega t → InZomega s →
      residue (t * s) = residueMultiply (residue t) (residue s)) ∧
    (∀ x : Residue, ∃ t : ℂ, InZomega t ∧ residue t = x) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P85

end
