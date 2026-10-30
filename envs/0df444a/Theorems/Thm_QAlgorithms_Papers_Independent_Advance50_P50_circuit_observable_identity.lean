-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_circuit_observable_identity
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.circuit_observable_identity
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:25:27.287033+00:00
-- url     : https://prove2.me/theorems/eb2a7f0f-27fe-4c7b-9305-02b7a2c76d6b
-- title:
--   Appendix D Eq.(D4): common observable for two distinct circuits
-- statement:
--   Let $U_1,U_2$ be exactly the three-qubit circuits of Fig.1(a),(b), transcribed as ordered lists of the printed gates. Wire $0$ is the ancilla, wires $1,2$ are the one-qubit data registers, and $W=T^\dagger H$ in circuit (b). Then
--
--   $$U_1^\dagger Z_0 U_1=U_2^\dagger Z_0 U_2=Z_0\,\mathrm{SWAP}_{1,2}.$$
--
--   These are statements about their common Heisenberg observable, with no assumption equating the unitaries or postulating the observable identity as input data.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 25, Appendix D Eq.(D4): common observable for two distinct circuits

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P50

open MeasureTheory ProbabilityTheory

open scoped ComplexConjugate ENNReal

-- Exact accepted primitives; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

-- Matrices carry the associative commutator bracket X*Y-Y*X.

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF pp.25–26, Eq.(D4): the two actual printed circuits have the same
Heisenberg observable, though their unitaries differ. -/
theorem circuit_observable_identity :
    circuit1.conjTranspose * siteEmbedding 0 pauliZ * circuit1 = targetObservable3 ∧
    circuit2.conjTranspose * siteEmbedding 0 pauliZ * circuit2 = targetObservable3 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
