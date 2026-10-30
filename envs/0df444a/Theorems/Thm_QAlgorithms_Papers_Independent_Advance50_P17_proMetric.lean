-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_proMetric
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.proMetric
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:24:22.489827+00:00
-- url     : https://prove2.me/theorems/d14ea759-0aa2-4589-934c-3a5ced345519
-- title:
--   Section IV A: process-state lifting preserves the metric property
-- statement:
--   Let $\mathcal E,\mathcal F$ range over CPTP maps on a fixed positive finite-dimensional system. Write $\rho_{\mathcal E}=(\mathcal I\otimes\mathcal E)(|\Phi_d\rangle\langle\Phi_d|)$, where $|\Phi_d\rangle=d^{-1/2}\sum_j|j\rangle|j\rangle$ has the reference register first. If $\Delta$ is a metric on normalized density matrices of this doubled register, then
--
--   $$\Delta_{\rm pro}(\mathcal E,\mathcal F)=\Delta(\rho_{\mathcal E},\rho_{\mathcal F})$$
--
--   is a metric on CPTP maps, including separation of distinct maps. This transfers state comparison to process comparison.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 5, Section IV A: process-state lifting preserves the metric property

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

/-- Section IV A, PDF p.5: Choi lifting preserves all metric axioms. -/
theorem proMetric (delta : FiniteStateDistance)
    (hm : MetricAxioms (fun rho sigma : ProcessDensityInput (I × I) => delta rho.val sigma.val)) :
    MetricAxioms (fun E F : FiniteProcess I I => proDistance delta E.val F.val) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
