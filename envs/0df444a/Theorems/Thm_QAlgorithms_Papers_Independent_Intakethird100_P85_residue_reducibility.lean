-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P85_residue_reducibility
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P85.residue_reducibility
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:09:28.766206+00:00
-- url     : https://prove2.me/theorems/cba291a6-8edd-4dbc-84b6-b846c119d405
-- title:
--   Lemma 2: equivalent residue reducibility tests
-- statement:
--   Let $A=\mathbb Z_2[\omega]$ with $\omega^4=1$, and write $pqrs$ for coefficients of $\omega^3,\omega^2,\omega,1$. For $x\in A$, reducible means $x=\sqrt2\,y$ for some $y\in A$, where the residue of $\sqrt2$ is $1010$. Then
--
--   $$
--   x\text{ reducible}\iff x\in\{0000,0101,1010,1111\}
--   \iff\sqrt2\,x=0000\iff x^\dagger x=0000.
--   $$
--
--   Moreover, $x$ is twice reducible, meaning $x=2y$ in $A$, if and only if $x=0000$.
--
--   These tests detect the residue classes permitting denominator reduction.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, PDF p. 3, Lemma 2: equivalent residue reducibility tests

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

/-- Lemma 2, PDF p.3: all four reducibility criteria and twice reducibility. -/
theorem residue_reducibility (x : Residue) :
    (Reducible x ↔ x ∈ ({bits 0, bits 5, bits 10, bits 15} : Set Residue)) ∧
    (Reducible x ↔ residueMultiply (bits 10) x = bits 0) ∧
    (Reducible x ↔ residueNorm x = bits 0) ∧
    (TwiceReducible x ↔ x = bits 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P85

end
