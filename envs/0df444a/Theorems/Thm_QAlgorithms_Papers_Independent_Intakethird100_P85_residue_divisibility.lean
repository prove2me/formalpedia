-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P85_residue_divisibility
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P85.residue_divisibility
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:09:59.913334+00:00
-- url     : https://prove2.me/theorems/d374bfd7-bbd6-4c55-92e4-446cd73556ee
-- title:
--   Lemma 3: divisibility detected by residues
-- statement:
--   Let $t\in\mathbb Z[\omega]$, and let $\rho(t)$ be its coefficient residue modulo $2$. Reducibility and twice reducibility mean divisibility in the residue algebra by the images of $\sqrt2$ and $2$, respectively. Then
--
--   $$
--   \frac t2\in\mathbb Z[\omega]\iff\rho(t)\text{ is twice reducible},\qquad
--   \frac t{\sqrt2}\in\mathbb Z[\omega]\iff\rho(t)\text{ is reducible}.
--   $$
--
--   The quotients are computed in $\mathbb C$ and tested for membership in the cyclotomic integer ring. This transfers divisibility questions to residues.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, PDF p. 3, Lemma 3: divisibility detected by residues

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

/-- Lemma 3, PDF p.3: quotients must belong to Z[omega]. -/
theorem residue_divisibility (t : ℂ) (integral : InZomega t) :
    (InZomega (t / 2) ↔ TwiceReducible (residue t)) ∧
    (InZomega (t / sqrtTwo) ↔ Reducible (residue t)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P85

end
