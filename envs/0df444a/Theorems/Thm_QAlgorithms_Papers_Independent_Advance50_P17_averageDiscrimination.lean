-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_averageDiscrimination
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.averageDiscrimination
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:29:44.226285+00:00
-- url     : https://prove2.me/theorems/851bde8f-8e56-4d88-8538-3604738f8b59
-- title:
--   Section IV B: operational interpretation of average trace distance
-- statement:
--   Let $\mathcal E,\mathcal F$ be CPTP maps on a positive finite-dimensional register. A normalized pure input $\psi$ is Haar-distributed and revealed before measurement. For density matrices $\rho,\sigma$, let $P_*(\rho,\sigma)$ be the supremum of $\tfrac12[\operatorname{tr}(M\rho)+\operatorname{tr}((I-M)\sigma)]$ over binary POVM effects $0\le M\le I$. Each pointwise optimum for $\rho=\mathcal E(\psi)$ and $\sigma=\mathcal F(\psi)$ is attained, and
--
--   $$\int P_*(\mathcal E(\psi),\mathcal F(\psi))\,d\psi=\frac12+\frac12D_{\rm ave}(\mathcal E,\mathcal F).$$
--
--   The optimizing measurement may depend on the revealed input.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 7, Section IV B: operational interpretation of average trace distance

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

/-- Section IV B, PDF p.7: input is revealed BEFORE optimizing its binary measurement.
The Haar average of pointwise optimal equal-prior success is 1/2+D_ave/2. -/
theorem averageDiscrimination (E F : FiniteProcess I I) :
    pureInputAverage (fun psi => optimalSuccess (E.val (pureDensity psi)) (F.val (pureDensity psi))) =
      1 / 2 + aveDistance (stateDistance .trace) E.val F.val / 2 ∧
    (∀ psi : ProcessPureInput I, ∃ M : Matrix I I ℂ, IsEffect M ∧
      binarySuccess (E.val (pureDensity psi.val)) (F.val (pureDensity psi.val)) M =
        optimalSuccess (E.val (pureDensity psi.val)) (F.val (pureDensity psi.val))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
