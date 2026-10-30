-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_postprocessing
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.postprocessing
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:20:32.684669+00:00
-- url     : https://prove2.me/theorems/49f25e78-812e-4add-9198-6a5b40384f39
-- title:
--   Section I: post-processing contractivity from metric and chaining
-- statement:
--   Let $\Delta$ be a family of metrics on finite-dimensional CPTP maps, satisfying chaining for all compatible compositions. For any fixed CPTP maps $\mathcal E,\mathcal F:I\to J$ and $\mathcal R:J\to K$, with all registers of positive finite dimension,
--
--   $$\Delta(\mathcal R\circ\mathcal E,\mathcal R\circ\mathcal F)\le\Delta(\mathcal E,\mathcal F).$$
--
--   Thus post-processing cannot increase process distinguishability.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 2, Section I: post-processing contractivity from metric and chaining

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

/-- Section I, PDF p.2: metric and chaining imply contractivity under arbitrary compatible
CPTP post-processing. The metric family is fixed before the processes. -/
theorem postprocessing (delta : ProcessDistance) (hm : ProcessMetrics delta)
    (hc : ProcessChaining delta) (E F : FiniteProcess I J) (R : FiniteProcess J K) :
    delta (R.val ∘ E.val) (R.val ∘ F.val) ≤ delta E.val F.val := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
