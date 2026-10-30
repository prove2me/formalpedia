-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_distanceOptimization
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.distanceOptimization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:38:24.181499+00:00
-- url     : https://prove2.me/theorems/a4a0e2e2-e907-44d7-8505-c2f940e8ceca
-- title:
--   Appendix A2: D_stab is an attained concave maximization
-- statement:
--   Fix CPTP maps $\mathcal E,\mathcal F$ on a positive finite-dimensional system. On the nonempty compact convex density-operator set $\mathcal D$, let $G_D(\rho)$ be the half trace-norm distance of the extended outputs on the canonical square-root purification of $\rho$. This objective is continuous and concave, and
--
--   $$D_{\rm stab}(\mathcal E,\mathcal F)=\max_{\rho\in\mathcal D}G_D(\rho).$$
--
--   The maximum is attained. The purified objective is distinct from the ordinarily convex distance $D(\mathcal E(\rho),\mathcal F(\rho))$.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 13, Appendix A2: D_stab is an attained concave maximization

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

/-- Appendix A2, PDF p.13: D_stab is an attained maximization of the continuous concave
PURIFIED trace-distance objective over normalized density operators. -/
theorem distanceOptimization (E F : FiniteProcess I I) :
    Set.Nonempty {rho : Matrix I I ℂ | IsDensityMatrix rho} ∧
    IsCompact {rho : Matrix I I ℂ | IsDensityMatrix rho} ∧
    Convex ℝ {rho : Matrix I I ℂ | IsDensityMatrix rho} ∧
    ContinuousOn (purifiedChannelTraceDistance E.val F.val) {rho | IsDensityMatrix rho} ∧
    ConcaveOn ℝ {rho | IsDensityMatrix rho} (purifiedChannelTraceDistance E.val F.val) ∧
    (∃ rho : ProcessDensityInput I, stabDistance (stateDistance .trace) E.val F.val =
      purifiedChannelTraceDistance E.val F.val rho.val ∧
      ∀ sigma : ProcessDensityInput I, purifiedChannelTraceDistance E.val F.val sigma.val ≤ purifiedChannelTraceDistance E.val F.val rho.val) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
