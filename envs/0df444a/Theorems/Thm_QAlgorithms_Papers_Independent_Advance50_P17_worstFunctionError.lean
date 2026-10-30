-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_worstFunctionError
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.worstFunctionError
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:19:24.464251+00:00
-- url     : https://prove2.me/theorems/093c4f0a-3006-4058-9077-9f6047eee1ab
-- title:
--   Section V A, Eqs.(19)–(20): worst-case function-computation error bounds
-- statement:
--   Let $\mathcal E,\mathcal F$ be fixed CPTP maps on a positive finite-dimensional register with computational basis indexed by $x$, and let $f(x)$ be the desired basis outcome. For $\mathcal G\in\{\mathcal E,\mathcal F\}$, put $e_{\mathcal G}=\max_x[1-\langle f(x)|\mathcal G(|x\rangle\langle x|)|f(x)\rangle]$. With $D_{\rm stab}$ the input-sized-ancilla maximum of half trace norm, $F_{\rm stab}$ the corresponding minimum squared fidelity, and $C_{\rm stab}=\sqrt{1-F_{\rm stab}}$, both bounds hold:
--
--   $$e_{\mathcal E}\le e_{\mathcal F}+D_{\rm stab}(\mathcal E,\mathcal F),\qquad e_{\mathcal E}\le\bigl(\sqrt{e_{\mathcal F}}+C_{\rm stab}(\mathcal E,\mathcal F)\bigr)^2.$$
--
--   These give worst-case operational error guarantees for a fixed real and ideal computation.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 9, Section V A, Eqs.(19)–(20): worst-case function-computation error bounds

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

/-- Section V A, PDF p.9, Eqs.(19)--(20), Appendix B1, p.13: BOTH worst-case
function-computation guarantees, using actual uniform worst-case ideal error. -/
theorem worstFunctionError (E F : FiniteProcess I I) (f : I → I) :
    worstFunctionErrorProbability E.val f ≤ worstFunctionErrorProbability F.val f + stabDistance (stateDistance .trace) E.val F.val ∧
    worstFunctionErrorProbability E.val f ≤ (Real.sqrt (worstFunctionErrorProbability F.val f) + stabC E.val F.val) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
