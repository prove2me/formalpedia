-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P02_bkFixedInputConvergence
-- name    : QAlgorithms.Papers.Independent.Intake100.P02.bkFixedInputConvergence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:52:19.9385+00:00
-- url     : https://prove2.me/theorems/24ae53b8-33c0-4ade-b182-2ab8e0cd5b12
-- title:
--   Pointwise fixed-input BK fidelity convergence
-- statement:
--   For every fixed finite input TMSV variance $t\ge1/2$, let $F(\mu,t)$ be the unsquared fidelity between that pure TMSV input and its reference-preserving BK output, independently constructed by Gaussian random displacements of variance $2\mu-\sqrt{4\mu^2-1}$. There exist constants $C>0$ and $\mu_0\ge1/2$, which may depend on $t$, such that
--
--   $$|1-F(\mu,t)|\le\frac{C}{\mu}\qquad(\mu\ge\mu_0),\qquad \lim_{\mu\to\infty}F(\mu,t)=1.$$
--
--   This is pointwise convergence at fixed input energy. It asserts neither uniform convergence over input energies nor trace-norm convergence of the resource sequence.
-- source:
--   Theory of channel simulation and bounds for private communication, arXiv:1711.09909v3, PDF p. 28, Appendix A, Eq. (A5): fixed-input BK convergence

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P02

open Filter MeasureTheory QAlgorithms

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Next46.P32 (complexNormal)

/-- arXiv:1711.09909v3, PDF p.28, Appendix A, (A5): fixed finite physical
input variance, root infidelity O(1/mu). Constants depend on t; no uniformity
in input energy or convergence of the resource state is asserted. -/
theorem bkFixedInputConvergence (t : ℝ) (ht : 1 / 2 ≤ t) :
    (∃ C mu0 : ℝ, 0 < C ∧ 1 / 2 ≤ mu0 ∧
      ∀ mu : ℝ, mu0 ≤ mu → |1 - bkRootFidelity mu t| ≤ C / mu) ∧
    Tendsto (fun mu : ℝ => bkRootFidelity mu t) atTop (𝓝 1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P02

end
