-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P44_example_swapping_optimum
-- name    : QAlgorithms.Papers.Independent.Claimed50.P44.example_swapping_optimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:12:27.92336+00:00
-- url     : https://prove2.me/theorems/e8eff610-dd2f-499d-b7a1-829c2a203299
-- title:
--   Process-score optimizer and strict dissipative advantage
-- statement:
--   For the same resource with $b_0=1/2$ and $r\ge0$, use the amplitude $t$ and noise level $n_*$ defined in the coherent-input example. The deterministic Bob attenuation $S=tI$, $G=(1-t^2)I$ maximizes the renormalized process score against every Bob Gaussian channel, including affine displacements, and also against every independent diagonal two-sided Gaussian strategy. Its score and the best Bob symplectic score are
--
--   $$\mathcal F_{\rm CP}=\frac{2}{n_*},\qquad \mathcal F_{\rm symp}=\frac{2}{1/2+2e^{-2r}}.$$
--
--   For every $r>0$, $\mathcal F_{\rm CP}>1$. In the open interval $0<r<-\tfrac12\log(3/4)$ every Bob symplectic unitary has score strictly below $1$, while the CP optimum has score above $1$. At $r=0$ the CP score is exactly $1$.
--
--   The two-sided comparison is restricted to the diagonal class; it does not assume the source's unproved general diagonal-optimality hypothesis.
-- source:
--   Improving fidelity of continuous-variable teleportation via local operations, arXiv:quant-ph/0202102v3, PDF p. 7, §IV, Fig.2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P44

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Claimed50.P44

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance pureCovariance)

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.7, Fig.2: the same damping maximizes the process score over all
Bob Gaussian maps, and over diagonal two-sided independent maps. Unrestricted
two-sided Gaussian optimality is not asserted. At r=0 the score is exactly 1. -/
theorem example_swapping_optimum (r : ℝ) (hr : 0 ≤ r) :
    let t := dampingGain r
    let W := exampleOutput r (t • (1 : QuadratureMatrix)) (dampingNoise r) 0
    GaussianCP (t • (1 : QuadratureMatrix)) (dampingNoise r) ∧
    processScore W = 2 / exampleOptimalNoise r ∧
    (∀ (S G : QuadratureMatrix) (d : PhasePoint), GaussianCP S G →
      processScore (exampleOutput r S G d) ≤ processScore W) ∧
    (∀ (S : QuadratureMatrix) (d : PhasePoint), Symplectic S →
      processScore (exampleOutput r S 0 d) ≤ processScore (exampleOutput r 1 0 0)) ∧
    processScore (exampleOutput r 1 0 0) = 2 / (1 / 2 + 2 * Real.exp (-2 * r)) ∧
    ValidStrategy (dampingStrategy r) ∧
    strategyScore (exampleResource r) (dampingStrategy r) = processScore W ∧
    (∀ s : DiagonalStrategy, ValidStrategy s →
      strategyScore (exampleResource r) s ≤ processScore W) ∧
    (0 < r → 1 < processScore W) ∧
    (0 < r → r < -Real.log (3 / 4) / 2 →
      ∀ (S : QuadratureMatrix) (d : PhasePoint), Symplectic S → processScore (exampleOutput r S 0 d) < 1) ∧
    (r = 0 → processScore W = 1) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P44

end
