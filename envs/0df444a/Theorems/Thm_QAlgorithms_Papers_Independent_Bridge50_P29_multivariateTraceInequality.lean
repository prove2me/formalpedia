-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P29_multivariateTraceInequality
-- name    : QAlgorithms.Papers.Independent.Bridge50.P29.multivariateTraceInequality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:32:50.552211+00:00
-- url     : https://prove2.me/theorems/4042d2ad-a118-4092-9363-3a9067561daf
-- title:
--   Multivariate trace inequality with semidefinite factors
-- statement:
--   Let $d\geq1$, $0<p\leq\infty$, $0<r\leq1$, and $n\in\mathbb N$. For any positive semidefinite complex $d\times d$ matrices $A_1,\ldots,A_n$, with products in the indicated order,
--
--   $$
--   \log\left\|\left|\prod_{k=1}^n A_k^r\right|^{1/r}\right\|_p
--   \leq
--   \int_{\mathbb R}\beta_r(t)\log\left\|\prod_{k=1}^n A_k^{1+it}\right\|_p\,dt.
--   $$
--
--   Here $|B|=(B^*B)^{1/2}$, $\|\cdot\|_p$ is the ordinary unnormalized Schatten quasi-norm (the operator norm at infinity), and $\beta_r(t)=\sin(\pi r)/[2r(\cosh(\pi t)+\cos(\pi r))]$ for $r<1$. At $r=1$ the averaging measure is $\delta_0$. Logarithms take the value $-\infty$ at zero; integrate positive and negative parts separately. Complex powers are spectral powers, zero on kernels for positive real part. The empty product is the identity. This inequality retains the modulus and outer power $1/r$ and applies without invertibility or state normalization.
-- source:
--   Interpolation of quasi noncommutative $L_p$-spaces, arXiv:1905.08491v1, PDF p. 14, Corollary 3.8

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

/-- Corollary 3.8, arXiv:1905.08491v1, PDF pp.14--15, Eq.(3.5).
The matrices are semidefinite, without invertibility or state normalization.
The left side is log || |product A_k^r|^(1/r) ||_p, retaining the essential
factor 1/r. At r=1 the beta average is evaluation at zero. n=0 is allowed. -/
theorem multivariateTraceInequality
    (d : ℕ) (hd : 0 < d) (p : ℝ≥0∞) (hp : 0 < p)
    (r : ℝ) (hr : 0 < r ∧ r ≤ 1) (n : ℕ)
    (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ k, (A k).PosSemidef) :
    extendedLog (schattenNorm p
      (modulusPower (orderedProduct (fun k => positiveComplexPower (A k) (r : ℂ)))
        (1 / r))) ≤
      betaLogAverage r (fun t => extendedLog (schattenNorm p
        (orderedProduct (fun k => positiveComplexPower (A k) (1 + (t : ℂ) * Complex.I))))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P29

end
