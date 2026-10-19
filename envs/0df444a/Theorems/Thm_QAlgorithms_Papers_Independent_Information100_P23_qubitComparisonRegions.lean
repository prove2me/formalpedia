-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P23_qubitComparisonRegions
-- name    : QAlgorithms.Papers.Independent.Information100.P23.qubitComparisonRegions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:12:21.790965+00:00
-- url     : https://prove2.me/theorems/a0e3af33-4392-434d-bdcc-74b2c275bb04
-- title:
--   §5 and §8.1: comparison regions, strictness, and non-sufficiency
-- statement:
--   Fix a normalized qubit Bloch basis. For a CPTP complex-linear qubit map, let $(A,c)$ be its computed Bloch data. Define three conditions
--
--   $$L:\ \|A\|_*+|c|\le1,\qquad Q:\ \|A\|_*^2+|c|^2\le1,\qquad O:\ \|A\|_{\mathrm{op}}^2+|c|^2\le1,$$
--
--   where the matrix norms are respectively the nuclear norm and the Euclidean operator norm. On CPTP maps, $L$ implies both entanglement breaking and $Q$, and $Q$ implies $O$. Both condition inclusions are strict: there is a CPTP map in $Q\setminus L$ and a CPTP map in $O\setminus Q$. There is also an EB CPTP map in $Q\setminus L$, and a CPTP map in $Q$ that is not EB.
--
--   These assertions locate the quadratic necessary condition between the credited linear sufficient condition and the operator-norm condition. The numerical count in the quotation is not asserted as a probability law.
-- source:
--   A sharp norm inequality for entanglement-breaking channels, arXiv:2609.27906v1, PDF p. 4, §5 and §8.1: comparison regions, strictness, and non-sufficiency

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P23

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P23

/-- PDF p.4, §5, and p.5, §8.1: implications, strict region inclusions, an EB
witness outside the linear sufficient region, and failure of quadratic sufficiency.
The reported sample counts are evidence, not a law for random channels. -/
theorem qubitComparisonRegions (B : BlochBasis 2) :
    (∀ Phi : ChannelMap 2, IsCPTP Phi → LinearCondition B Phi →
      Entanglement.IsEntanglementBreakingPositive Phi ∧ QuadraticCondition B Phi) ∧
    (∀ Phi : ChannelMap 2, IsCPTP Phi → QuadraticCondition B Phi → OperatorCondition B Phi) ∧
    (∃ Phi : ChannelMap 2, IsCPTP Phi ∧ QuadraticCondition B Phi ∧ ¬ LinearCondition B Phi) ∧
    (∃ Phi : ChannelMap 2, IsCPTP Phi ∧ OperatorCondition B Phi ∧ ¬ QuadraticCondition B Phi) ∧
    (∃ Phi : ChannelMap 2, IsCPTP Phi ∧ Entanglement.IsEntanglementBreakingPositive Phi ∧
      QuadraticCondition B Phi ∧ ¬ LinearCondition B Phi) ∧
    (∃ Phi : ChannelMap 2, IsCPTP Phi ∧ QuadraticCondition B Phi ∧
      ¬ Entanglement.IsEntanglementBreakingPositive Phi) := by sorry

end QAlgorithms.Papers.Independent.Information100.P23

end
