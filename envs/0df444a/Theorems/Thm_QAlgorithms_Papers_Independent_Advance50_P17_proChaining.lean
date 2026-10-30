-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_proChaining
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.proChaining
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:25:49.685165+00:00
-- url     : https://prove2.me/theorems/4a60f403-db8b-418a-a9e0-110840cec197
-- title:
--   Section IV A, Eqs.(7)–(9): process-matrix chaining with a unital ideal first step
-- statement:
--   Let $\Delta$ be a state-metric family contractive under finite-dimensional CPTP maps. Let $\mathcal E_1,\mathcal F_1,\mathcal E_2,\mathcal F_2$ be CPTP maps on a positive finite-dimensional system, and assume $\mathcal F_1(I)=I$. For normalized Choi-state distances,
--
--   $$\Delta_{\rm pro}(\mathcal E_2\circ\mathcal E_1,\mathcal F_2\circ\mathcal F_1)\le\Delta_{\rm pro}(\mathcal E_2,\mathcal F_2)+\Delta_{\rm pro}(\mathcal E_1,\mathcal F_1).$$
--
--   Only the first ideal step must be unital; the second ideal step may be any CPTP map.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 6, Section IV A, Eqs.(7)–(9): process-matrix chaining with a unital ideal first step

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

/-- Section IV A, PDF pp.5--6, Eqs.(7)--(9): chaining requires the IDEAL FIRST step to be unital.
F2 is arbitrary CPTP. The Section VI abbreviation does not remove this condition. -/
theorem proChaining (delta : FiniteStateDistance) (hm : StateMetrics delta)
    (hc : StateContractive delta) (E1 F1 E2 F2 : FiniteProcess I I) (hu : F1.val 1 = 1) :
    proDistance delta (E2.val ∘ E1.val) (F2.val ∘ F1.val) ≤
      proDistance delta E2.val F2.val + proDistance delta E1.val F1.val := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
