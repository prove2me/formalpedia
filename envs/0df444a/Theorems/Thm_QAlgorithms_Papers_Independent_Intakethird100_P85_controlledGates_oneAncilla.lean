-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P85_controlledGates_oneAncilla
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P85.controlledGates_oneAncilla
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:14:24.502065+00:00
-- url     : https://prove2.me/theorems/342d9405-41ad-49a7-bf68-9ebee8ae13c6
-- title:
--   §5.2, unnumbered: controlled X,H,T with one ancilla
-- statement:
--   Let $r\ge0$ be a number of positive controls and let $M\in\{X,H,T\}$. Let $\Lambda^r(M)$ apply $M$ to its target precisely when every control is $1$, and otherwise act as the identity. There is an elementary Clifford+T circuit $C$ on $r+2$ wires such that, for every input vector $\psi$ on the $r+1$ data wires,
--
--   $$U_C(\psi\otimes|0\rangle)=\Lambda^r(M)\psi\otimes|0\rangle.$$
--
--   The helper is trailing and returns exactly to zero. With $r=0$, the controlled operation is simply $M$. These implementations establish the one-ancilla sufficiency step.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, PDF p. 5, §5.2, unnumbered: controlled X,H,T with one ancilla

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

/-- Section 5.2, PDF p.5: all positive multiply-controlled X,H,T gates use one clean helper. -/
theorem controlledGates_oneAncilla :
    ∀ r : ℕ, ∀ M ∈ ({pauliX, hadamard, gateT} : Set (Matrix Bool Bool ℂ)),
      ∃ c : Circuit gateSet ((r + 1) + 1),
        ImplementsWithCleanAncillas c.unitary (multiplyControlled r M) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P85

end
