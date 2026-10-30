-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_stabilizedMetricChaining
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.stabilizedMetricChaining
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:35:07.439442+00:00
-- url     : https://prove2.me/theorems/2037b088-97a9-4b86-8df1-b117071c296b
-- title:
--   Section IV C: stabilized metrics satisfy metric and chaining criteria
-- statement:
--   For every positive finite-dimensional register and each $\Delta\in\{D,A,B,C\}$, $\Delta_{\rm stab}$ is a metric on CPTP maps. For any four CPTP steps on that register,
--
--   $$\Delta_{\rm stab}(\mathcal E_2\circ\mathcal E_1,\mathcal F_2\circ\mathcal F_1)\le\Delta_{\rm stab}(\mathcal E_1,\mathcal F_1)+\Delta_{\rm stab}(\mathcal E_2,\mathcal F_2).$$
--
--   No step is required to be unital. The scope is the four concrete contractive, isometry-invariant state metrics.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 8, Section IV C: stabilized metrics satisfy metric and chaining criteria

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P17

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Advance50.P17

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P75 (hermitianReal)

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]
  [Nonempty I] [Nonempty J] [Nonempty K]

/-- Section IV C, PDF p.8: stabilized concrete metrics are metrics and chain for all CPTP
steps, with no unitality requirement. -/
theorem stabilizedMetricChaining (c : Choice) :
    MetricAxioms (fun E F : FiniteProcess I I => stabDistance (stateDistance c) E.val F.val) ∧
    (∀ E1 F1 E2 F2 : FiniteProcess I I,
      stabDistance (stateDistance c) (E2.val ∘ E1.val) (F2.val ∘ F1.val) ≤
        stabDistance (stateDistance c) E1.val F1.val +
        stabDistance (stateDistance c) E2.val F2.val) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
