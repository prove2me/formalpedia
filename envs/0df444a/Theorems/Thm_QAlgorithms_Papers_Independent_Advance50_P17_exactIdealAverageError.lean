-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_exactIdealAverageError
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.exactIdealAverageError
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:40:22.222289+00:00
-- url     : https://prove2.me/theorems/c9baac08-6f4f-4606-b52e-92eebc1e72a2
-- title:
--   Section V A, Eq.(22), Appendix B2: average error controlled by J infidelity when ideal computation is exact
-- statement:
--   Let $\mathcal E,\mathcal F$ be CPTP on a positive finite-dimensional system and let $f$ prescribe a computational-basis output for every basis input. Let $\bar e_{\mathcal G}$ be its uniform finite-instance mean error. If $\bar e_{\mathcal F}=0$, equivalently the ideal computation is exact on every input, then
--
--   $$\bar e_{\mathcal E}\le C_{\rm pro}(\mathcal E,\mathcal F)^2=1-F_{\rm pro}(\mathcal E,\mathcal F).$$
--
--   Here $F_{\rm pro}$ is squared fidelity of normalized Choi states. The exact-ideal premise is essential.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 9, Section V A, Eq.(22), Appendix B2: average error controlled by J infidelity when ideal computation is exact

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

/-- Section V A, PDF p.9, Eq.(22), Appendix B2, p.14: exact ideal computation is essential.
The source's unadorned F here is F_pro, as forced by C_pro squared. -/
theorem exactIdealAverageError (E F : FiniteProcess I I) (f : I → I) (h : meanError F.val f = 0) :
    meanError E.val f ≤ proDistance (stateDistance .sine) E.val F.val ^ 2 ∧
    proDistance (stateDistance .sine) E.val F.val ^ 2 = 1 - proFidelity E.val F.val := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
