-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_geometric_qubit_catalysis
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.geometric_qubit_catalysis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:13:31.297565+00:00
-- url     : https://prove2.me/theorems/38332bdc-5eae-4e49-bc53-eb806b5106ab
-- title:
--   One-qubit catalysis with constrained geometry
-- statement:
--   Let n≥1 qubits form an open chain and let V be any invariant unitary. Exact coherent catalysis by one ground-state qubit is possible in each of two control geometries: (a) adjacent system exchange, ancilla exchange with every site, and ancilla Z; (b) adjacent system exchange and ZZ, exchange and ZZ between the ancilla and the first site only, and ancilla Z. In each case there is a finite-product W with
--
--   $$W(|\psi\rangle|0\rangle_a)=(V|\psi\rangle)|0\rangle_a\quad\text{for all }\psi.$$
--
--   Both conclusions use one common circuit for all system inputs.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 40, G.2: one ancilla with constrained interaction geometry

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF pp.40–42, G4–G7: both geometries. G4's shortened ancilla index range
j=1,...,n-1 is corrected to all system sites for ancilla couplings, as the
immediately preceding prose requires; G7 retains the ancilla-endpoint ZZ control. -/
theorem geometric_qubit_catalysis (n : ℕ) (hn : 1 ≤ n) (V : QMat n) (hV : U1Unitary V) :
    (∃ W : QMat (n+1), W ∈ controlGenerated (geometricCatalystControls n false) ∧ Catalyzes W V) ∧
    (∃ W : QMat (n+1), W ∈ controlGenerated (geometricCatalystControls n true) ∧ Catalyzes W V) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P14

end
