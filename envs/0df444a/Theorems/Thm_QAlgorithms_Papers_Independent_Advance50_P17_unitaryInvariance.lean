-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_unitaryInvariance
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.unitaryInvariance
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:21:42.453545+00:00
-- url     : https://prove2.me/theorems/dd6d9070-0577-4527-a9ec-df0fe8234d97
-- title:
--   Section I: unitary invariance from metric and chaining
-- statement:
--   Let $\Delta$ be a chaining family of metrics on finite-dimensional CPTP maps. Let $\mathcal E,\mathcal F:I\to J$ be CPTP, and let $U$ and $V$ be unitaries on $J$ and $I$, respectively. Writing $\mathcal U$ and $\mathcal V$ for their conjugation channels,
--
--   $$\Delta(\mathcal U\circ\mathcal E\circ\mathcal V,\mathcal U\circ\mathcal F\circ\mathcal V)=\Delta(\mathcal E,\mathcal F).$$
--
--   The statement applies to arbitrary positive finite input and output dimensions.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 2, Section I: unitary invariance from metric and chaining

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

/-- Section I, PDF p.2: unitary pre- and post-processing preserve every chaining process metric. -/
theorem unitaryInvariance (delta : ProcessDistance) (hm : ProcessMetrics delta)
    (hc : ProcessChaining delta) (E F : FiniteProcess I J)
    (U : Matrix.unitaryGroup J ℂ) (V : Matrix.unitaryGroup I ℂ) :
    delta (conjSuperop (U : Matrix J J ℂ) ∘ E.val ∘ conjSuperop (V : Matrix I I ℂ))
      (conjSuperop (U : Matrix J J ℂ) ∘ F.val ∘ conjSuperop (V : Matrix I I ℂ)) =
        delta E.val F.val := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
