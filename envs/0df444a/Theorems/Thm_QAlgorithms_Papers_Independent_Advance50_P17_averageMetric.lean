-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_averageMetric
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.averageMetric
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:29:04.853336+00:00
-- url     : https://prove2.me/theorems/97386aa0-9eb8-47fa-b4f8-801fac0da366
-- title:
--   Section IV B, Eq.(13): Haar average is a process metric
-- statement:
--   Let $\Delta$ be a state metric continuous on normalized density matrices, and let $\mathcal E,\mathcal F$ range over CPTP maps on a fixed positive finite-dimensional system. With normalized Haar measure on pure inputs,
--
--   $$\Delta_{\rm ave}(\mathcal E,\mathcal F)=\int\Delta(\mathcal E(\psi),\mathcal F(\psi))\,d\psi$$
--
--   has an integrable integrand and is a metric on processes, including separation of distinct channels. Here $\psi$ denotes the rank-one density of a unit vector. Continuity supplies the regularity implicit in the source's integral.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 7, Section IV B, Eq.(13): Haar average is a process metric

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

/-- Section IV B, PDF p.7, Eq.(13): a continuous state metric gives an integrable, faithful
Haar-averaged process metric. Continuity is on density matrices, not on arbitrary operators. -/
theorem averageMetric (delta : FiniteStateDistance) (hm : StateMetrics delta)
    (hcont : StateContinuous delta) :
    MetricAxioms (fun E F : FiniteProcess I I => aveDistance delta E.val F.val) ∧
    (∀ E F : FiniteProcess I I, Integrable (fun U => delta
      (E.val (pureDensity (haarColumnInput (I := I) U)))
      (F.val (pureDensity (haarColumnInput (I := I) U)))) (Schur.unitaryHaar (Fintype.card I))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
