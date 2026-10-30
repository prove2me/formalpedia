-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_qubit_catalysis
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.qubit_catalysis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:01:50.011768+00:00
-- url     : https://prove2.me/theorems/871e5012-886b-4cdc-8edc-218d44a5084a
-- title:
--   One-qubit exact U(1) catalysis with ancilla-only Z
-- statement:
--   Let n≥1 and let V be an invariant n-qubit unitary. There is a unitary W on the system and one qubit ancilla that is a finite product of exchange evolutions exp(iθ(XX+YY)/2) on arbitrary pairs and exp(iθZ_a) on the ancilla alone, such that
--
--   $$W(|\psi\rangle\otimes|0\rangle_a)=(V|\psi\rangle)\otimes|0\rangle_a\quad\text{for every }|\psi\rangle.$$
--
--   The same W returns the ancilla exactly and coherently, including the physical global phase of V.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 5, II.D / G.2: one-qubit catalyst and XX+YY with local ancilla Z

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF pp.5,40–41, Eq.6/G2–G3: only ancilla Z is needed; the ancilla is
returned coherently and exactly for all inputs, including global phase. -/
theorem qubit_catalysis (n : ℕ) (hn : 1 ≤ n) (V : QMat n) (hV : U1Unitary V) :
    ∃ W : QMat (n+1), W ∈ controlGenerated (qubitCatalystControls n) ∧ Catalyzes W V := by sorry

end QAlgorithms.Papers.Independent.Extend50.P14

end
