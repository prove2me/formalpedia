-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P06_absorbingDiffusion_heatKernel
-- name    : QAlgorithms.Papers.Independent.Renew46.P06.absorbingDiffusion_heatKernel
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:52:13.757433+00:00
-- url     : https://prove2.me/theorems/824dee18-b5ff-4d74-b652-d8bf8580fa09
-- title:
--   Reflected heat kernel for the minimal absorbing diffusion
-- statement:
--   Let $S_t^0$ be the actual minimal absorbing diffusion on the complex trace class of $H=L^2(\mathbb R_+)$. For a trace-class input $\rho$, let $k$ be any $L^2$ kernel representing its integral-operator action. For every $t>0$, the output has a representative $k_t$ such that, for almost every $(x,y)\in\mathbb R_+^2$,
--
--   $$
--   \begin{aligned}
--   k_t(x,y)=\frac1{2\sqrt{\pi t}}\int_0^\infty
--   \Bigl[\exp\!\left(-\frac{|\min(x,y)-\xi|^2}{4t}\right)
--   -\exp\!\left(-\frac{|\min(x,y)+\xi|^2}{4t}\right)\Bigr]\\
--   {}\times k\bigl(\xi+[x-y]_+,\xi+[y-x]_+\bigr)\,d\xi,
--   \qquad [a]_+=\max(a,0).
--   \end{aligned}
--   $$
--
--   The displayed integrand is integrable for almost every $(x,y)$. At time zero the evolution is the identity, and its orbits are continuous in trace norm. The positive-time integral is not evaluated by division at $t=0$; the reflection difference gives zero absorbing boundary trace for the suitable representative.
--
--   This is the paper's corrected formula (30), replacing the earlier erroneous expression cited there.
-- source:
--   On singular perturbations of quantum dynamical semigroups, arXiv:1706.04866v5, PDF p. 12, §3.3, unnumbered result (30): reflected heat-kernel formula for the absorbing diffusion

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P06

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Renew46.P06

open QAlgorithms.Papers.Independent.Dependency50.P13
  (TraceClass State NuclearRepresentation traceNormValue operatorTrace)

open QAlgorithms.Papers.Independent.Claimed50.P50
  (ContractionSemigroup DynamicalSemigroup IsCPOnBoundedOperators
    IsUnitalQDS IsRelaxingEvolution)

open QAlgorithms.Papers.Independent.Next46.P09
  (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain
    DomainPerturbation IsMinimalPerturbation)

/-- PDF pp.11–12, (30): the corrected reflected Poisson integral for the actual minimal
absorbing evolution, at positive times and almost every (x,y). Every integral is guarded
by integrability. No arbitrary pointwise representative or t=0 division is used. -/
theorem absorbingDiffusion_heatKernel (b : HilbertBasis ℕ ℂ HalfLine)
    (Szero : TraceEvolution b) (Tzero : Evolution)
    (hDiffusion : IsAbsorbingDiffusion Tzero) (hPair : IsPredual b Szero Tzero)
    (rho : (TraceClass HalfLine)) (k : ℝ × ℝ → ℂ) (hKernel : HasKernel rho k)
    (t : ℝ) (ht : 0 < t) :
    ∃ kt : ℝ × ℝ → ℂ, HasKernel (Szero.maps t.toNNReal rho) kt ∧
      (∀ᵐ p : ℝ × ℝ ∂halfLineMeasure.prod halfLineMeasure,
        Integrable (fun xi =>
          (reflectedWeight t (min p.1 p.2) xi : ℂ) *
            k (xi + max (p.1 - p.2) 0, xi + max (p.2 - p.1) 0)) halfLineMeasure ∧ kt p = heatKernel t k p) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P06

end
