-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_fidelityOptimization
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.fidelityOptimization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:37:46.626079+00:00
-- url     : https://prove2.me/theorems/ceb90125-71eb-467e-ad5f-25daa100eaa7
-- title:
--   Appendix A2: F_stab is an attained convex minimization
-- statement:
--   Fix CPTP maps $\mathcal E,\mathcal F$ on a positive finite-dimensional system. The density-operator set $\mathcal D$ is nonempty, compact, and convex. The squared fidelity $G_F(\rho)$ of the two extended outputs on the canonical square-root purification is continuous and convex on $\mathcal D$, and
--
--   $$F_{\rm stab}(\mathcal E,\mathcal F)=\min_{\rho\in\mathcal D}G_F(\rho).$$
--
--   The minimum is attained, and every local minimum relative to $\mathcal D$ is global. This is a convex-optimization characterization without a numerical runtime or accuracy claim.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 12, Appendix A2: F_stab is an attained convex minimization

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

/-- Appendix A2, PDF pp.12--13: F_stab is an attained minimization of a continuous convex
objective on the nonempty compact convex density set; local minima are global. -/
theorem fidelityOptimization (E F : FiniteProcess I I) :
    Set.Nonempty {rho : Matrix I I ℂ | IsDensityMatrix rho} ∧
    IsCompact {rho : Matrix I I ℂ | IsDensityMatrix rho} ∧
    Convex ℝ {rho : Matrix I I ℂ | IsDensityMatrix rho} ∧
    ContinuousOn (purifiedFidelity E.val F.val) {rho | IsDensityMatrix rho} ∧
    ConvexOn ℝ {rho | IsDensityMatrix rho} (purifiedFidelity E.val F.val) ∧
    (∃ rho : ProcessDensityInput I, stabFidelity E.val F.val = purifiedFidelity E.val F.val rho.val ∧
      ∀ sigma : ProcessDensityInput I, purifiedFidelity E.val F.val rho.val ≤ purifiedFidelity E.val F.val sigma.val) ∧
    (∀ rho : ProcessDensityInput I, IsLocalMinOn (purifiedFidelity E.val F.val)
      {sigma | IsDensityMatrix sigma} rho.val →
        ∀ sigma : ProcessDensityInput I, purifiedFidelity E.val F.val rho.val ≤ purifiedFidelity E.val F.val sigma.val) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
