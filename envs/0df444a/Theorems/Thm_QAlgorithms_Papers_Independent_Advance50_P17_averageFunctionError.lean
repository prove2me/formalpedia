-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_averageFunctionError
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.averageFunctionError
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:39:05.330669+00:00
-- url     : https://prove2.me/theorems/63ec9e90-5e23-4389-97b1-504164f03b1b
-- title:
--   Section V A, Eq.(21), Appendix B2: average function error controlled by J distance
-- statement:
--   Let $\mathcal E,\mathcal F$ be fixed CPTP maps on a $d$-dimensional system, $d\ge1$, with all computational basis inputs $x$ equally likely, and let $f(x)$ be the desired basis outcome. Define $\bar e_{\mathcal G}=d^{-1}\sum_x[1-\langle f(x)|\mathcal G(|x\rangle\langle x|)|f(x)\rangle]$. Then
--
--   $$\bar e_{\mathcal E}\le\bar e_{\mathcal F}+D_{\rm pro}(\mathcal E,\mathcal F).$$
--
--   The process distance uses normalized Choi states. This concerns a finite uniform input average, not Haar inputs or a freely chosen input distribution.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 9, Section V A, Eq.(21), Appendix B2: average function error controlled by J distance

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

/-- Section V A, PDF p.9, Eq.(21), Appendix B2, pp.13--14: uniform finite-input mean error. -/
theorem averageFunctionError (E F : FiniteProcess I I) (f : I → I) :
    meanError E.val f ≤ meanError F.val f + proDistance (stateDistance .trace) E.val F.val := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
