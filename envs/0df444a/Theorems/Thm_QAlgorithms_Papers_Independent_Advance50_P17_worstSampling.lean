-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_worstSampling
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.worstSampling
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:41:00.862647+00:00
-- url     : https://prove2.me/theorems/fb60a9da-49e1-4491-ae82-98b3cd9dbfc0
-- title:
--   Section V B, Eqs.(23)–(24), Appendix B3: worst-case sampling error
-- statement:
--   Let $\mathcal E,\mathcal F$ be fixed CPTP maps on a positive finite register. Measuring their outputs on each computational-basis input $x$ gives distributions $q_x$ and $p_x$, respectively. For distributions $r,s$, define $\operatorname{TV}(r,s)=\frac12\sum_y|r(y)-s(y)|$ and the unsquared overlap $\operatorname{BC}(r,s)=\sum_y\sqrt{r(y)s(y)}$. Then
--
--   $$\max_x\operatorname{TV}(q_x,p_x)\le D_{\rm stab}(\mathcal E,\mathcal F),\qquad\max_x[1-\operatorname{BC}(q_x,p_x)]\le C_{\rm stab}(\mathcal E,\mathcal F)^2.$$
--
--   Both guarantees are uniform over the full basis input set; classical overlap is not silently squared.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 10, Section V B, Eqs.(23)–(24), Appendix B3: worst-case sampling error

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

/-- Section V B, PDF p.10, Eqs.(23)--(24), Appendix B3, p.14: maximum over all basis inputs.
Classical F is the UNSQUARED Bhattacharyya overlap, including in the fidelity inequality. -/
theorem worstSampling (E F : FiniteProcess I I) :
    sSup (Set.range (fun x => classicalVariation (basisOutputLaw E.val x) (basisOutputLaw F.val x))) ≤
      stabDistance (stateDistance .trace) E.val F.val ∧
    sSup (Set.range (fun x => 1 - bhattacharyya (basisOutputLaw E.val x) (basisOutputLaw F.val x))) ≤
      stabC E.val F.val ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
