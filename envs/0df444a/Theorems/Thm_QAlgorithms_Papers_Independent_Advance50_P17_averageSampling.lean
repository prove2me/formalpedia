-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_averageSampling
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.averageSampling
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:41:32.007696+00:00
-- url     : https://prove2.me/theorems/50db32f9-87ce-4169-ba22-0e4b595bc6e4
-- title:
--   Section V B, Eqs.(25)–(26): average sampling error for joint input/output laws
-- statement:
--   For fixed CPTP maps $\mathcal E,\mathcal F$ on a $d$-dimensional register, $d\ge1$, let $q_x(y),p_x(y)$ be their computational-basis output probabilities. Under uniform basis inputs, define the joint laws $q(x,y)=q_x(y)/d$ and $p(x,y)=p_x(y)/d$. With $\operatorname{TV}(q,p)=\frac12\sum_{x,y}|q(x,y)-p(x,y)|$ and $\operatorname{BC}(q,p)=\sum_{x,y}\sqrt{q(x,y)p(x,y)}$,
--
--   $$\operatorname{TV}(q,p)\le D_{\rm pro}(\mathcal E,\mathcal F),\qquad 1-\operatorname{BC}(q,p)\le C_{\rm pro}(\mathcal E,\mathcal F)^2.$$
--
--   These compare joint input/output laws, without an exact-function or unitary-ideal premise.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 10, Section V B, Eqs.(25)–(26): average sampling error for joint input/output laws

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

/-- Section V B, PDF p.10, Eqs.(25)--(26): compare JOINT input/output laws under uniform
inputs. No exact-function or unitary-ideal premise is required. -/
theorem averageSampling (E F : FiniteProcess I I) :
    classicalVariation (jointLaw E.val) (jointLaw F.val) ≤ proDistance (stateDistance .trace) E.val F.val ∧
    1 - bhattacharyya (jointLaw E.val) (jointLaw F.val) ≤
      proDistance (stateDistance .sine) E.val F.val ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
