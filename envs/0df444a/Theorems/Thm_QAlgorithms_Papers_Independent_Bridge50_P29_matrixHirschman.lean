-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P29_matrixHirschman
-- name    : QAlgorithms.Papers.Independent.Bridge50.P29.matrixHirschman
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:32:00.497589+00:00
-- url     : https://prove2.me/theorems/244c4e29-75da-4b69-99cc-ba7b82c4fb13
-- title:
--   Hirschman interpolation for all positive Schatten exponents
-- statement:
--   Let $d\geq1$, and let $G$ be a bounded function from the closed strip into the complex $d\times d$ matrices, continuous on the closed strip in operator norm and analytic inside. Fix $0<p_0<p_1\leq\infty$ and $\theta\in[0,1]$, with $1/p_\theta=(1-\theta)/p_0+\theta/p_1$. Write $\|\cdot\|_p$ for the ordinary unnormalized Schatten quasi-norm and use the spectral operator norm at infinity. Then
--
--   $$
--   \log\|G(\theta)\|_{p_\theta}\leq
--   \int_{\mathbb R}\beta_{1-\theta}(t)\log\bigl(\|G(it)\|_{p_0}^{1-\theta}\bigr)\,dt+
--   \int_{\mathbb R}\beta_\theta(t)\log\bigl(\|G(1+it)\|_{p_1}^{\theta}\bigr)\,dt,
--   \qquad
--   \beta_s(t)=\frac{\sin(\pi s)}{2s(\cosh(\pi t)+\cos(\pi s))}\quad(0<s<1).
--   $$
--
--   Use $\log0=-\infty$. The integrals have finite positive parts and may have infinite negative parts. At the endpoints, $\beta_1(t)dt$ means $\delta_0$, and $\beta_0(t)dt$ has density $\pi/[2(\cosh(\pi t)+1)]$. These are the weak-limit endpoint interpretations of the printed kernel. This is the logarithmic refinement of the Schatten three-lines inequality, including the quasi-Banach range.
-- source:
--   Interpolation of quasi noncommutative $L_p$-spaces, arXiv:1905.08491v1, PDF p. 14, Proposition 3.7

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P29

noncomputable section

open MeasureTheory

open scoped ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Bridge50.P29

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Next46.P33
  (PositivePart Weight IsNormalWeight IsFaithfulWeight IsSemifiniteWeight positiveOne)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Dependency50.P21
  (extendedLog upperLogIntegral betaDensity betaZero interpolationExponent spectralFunction)

-- The frozen closedStrip is exactly the strip used in Section 2.4, PDF p.9.

open QAlgorithms.Papers.Independent.Support21.P21 (closedStrip)

/-- Proposition 3.7, arXiv:1905.08491v1, PDF p.14, Eq.(3.4).
Ordinary unnormalized Schatten quasi-norms include every p>0 and the
operator norm at infinity. Powers 1-theta and theta remain inside the logs.
Endpoint beta averages are their weak-limit measures, not the zero value
of the raw density formula at s=1. No nonzero or integrability hypothesis
is added to G. -/
theorem matrixHirschman
    (d : ℕ) (hd : 0 < d) (G : ℂ → Matrix (Fin d) (Fin d) ℂ)
    (hG : IsStripAnalytic G)
    (p0 p1 : ℝ≥0∞) (hp0 : 0 < p0) (hpp : p0 < p1)
    (theta : ℝ) (htheta : 0 ≤ theta ∧ theta ≤ 1) :
    extendedLog (schattenNorm (interpolationExponent theta p0 p1) (G (theta : ℂ))) ≤
      betaLogAverage (1 - theta) (fun t =>
        extendedLog ((schattenNorm p0 (G ((t : ℂ) * Complex.I))) ^ (1 - theta))) +
      betaLogAverage theta (fun t =>
        extendedLog ((schattenNorm p1 (G (1 + (t : ℂ) * Complex.I))) ^ theta)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P29

end
