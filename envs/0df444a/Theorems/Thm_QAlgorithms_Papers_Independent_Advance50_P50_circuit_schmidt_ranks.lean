-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_circuit_schmidt_ranks
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.circuit_schmidt_ranks
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:26:11.855038+00:00
-- url     : https://prove2.me/theorems/81a71a57-0a7f-4e3c-8cb5-973f84296827
-- title:
--   Appendix D: distinct operator Schmidt ranks
-- statement:
--   For the two actual three-qubit circuit unitaries $U_1,U_2$ in Fig.1, take the ancilla versus two-data-qubit operator bipartition. The operator Schmidt rank is the matrix rank after realignment with ancilla output/input as row indices and data output/input as column indices. Then
--
--   $$\operatorname{OSR}(U_1)=2,\qquad\operatorname{OSR}(U_2)=3.$$
--
--   Consequently no left-and-right local unitaries across that cut map $U_1$ to $U_2$. The conclusion concerns local unitary equivalence, not arbitrary irreversible local operations.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 26, Appendix D: distinct operator Schmidt ranks

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

/-- PDF p.26, Appendix D: the operator Schmidt ranks differ, precluding
local unitary equivalence; irreversible local operations are not included.
Printed: PDF p.26 infers that no local operations map the two circuits from their operator Schmidt ranks 2 and 3.
Changed: Make circuit equivalence explicit as left and right local unitary gates across ancilla versus data, V=(A tensor B) U (C tensor D); retain both exact operator Schmidt ranks.
Why: In context the objects being compared are unitary circuits. Local changes of their input and output bases are reversible unitary gates, under which operator Schmidt rank is invariant. The statement does not interpret local operations as irreversible state preparation or an arbitrary bipartite superchannel. -/
theorem circuit_schmidt_ranks :
    operatorSchmidtRank circuit1 = 2 ∧ operatorSchmidtRank circuit2 = 3 ∧
    ¬ LocallyEquivalent circuit1 circuit2 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
