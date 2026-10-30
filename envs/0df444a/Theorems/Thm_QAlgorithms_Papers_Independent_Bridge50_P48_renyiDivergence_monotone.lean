-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P48_renyiDivergence_monotone
-- name    : QAlgorithms.Papers.Independent.Bridge50.P48.renyiDivergence_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:56:08.719625+00:00
-- url     : https://prove2.me/theorems/c7471942-9f6d-422b-a22b-a850a11e8d58
-- title:
--   Monotonicity of the sandwiched relative Rényi entropy
-- statement:
--   Let $\mathcal H$ and $\mathcal K$ be complex Hilbert spaces, and let $\rho,\sigma$ be nonnegative trace-class operators on $\mathcal H$, with $0<\operatorname{Tr}\rho<\infty$. The operator $\sigma$ may be zero, and neither operator must have trace one. Let $\mathcal E$ be a completely positive, trace-preserving complex-linear map on trace-class operators from $\mathcal H$ to $\mathcal K$. For every order $\alpha\in[1/2,\infty]$,
--
--   $$D_\alpha(\rho\Vert\sigma)\ge D_\alpha(\mathcal E(\rho)\Vert\mathcal E(\sigma)).$$
--
--   Here $D_\alpha$ uses natural logarithms. For finite $\alpha\ne1$ it is $(\alpha-1)^{-1}\log(Q_\alpha(\rho,\sigma)/\operatorname{Tr}\rho)$, where $Q_\alpha$ is the extended spectral trace of the whole sandwiched operator raised to the power $\alpha$. At order one it is the extended Umegaki relative entropy divided by $\operatorname{Tr}\rho$. At infinity it is $\log\inf\{c>0:\rho\le c\sigma\}$, with no trace divisor. Failed support inclusion gives positive infinity at orders at least one; orthogonal supports also give positive infinity below one. No support inclusion is assumed.
--
--   This is data processing for the actual quantum operation on the full Hilbert-space domain.
-- source:
--   Monotonicity of a relative Rényi entropy, arXiv:1306.5358v3, PDF p. 2, Theorem 1 (Monotonicity)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P48

noncomputable section

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Bridge50.P48

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsPositive IsTraceClass operatorTrace)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Frank--Lieb, PDF p.2, Theorem 1; proof on PDF pp.2--3.
An actual completely positive trace-preserving map acts on all trace-class
inputs. No support inclusion or normalization to trace one is assumed.
The endpoint orders one and infinity are both included. -/
theorem renyiDivergence_monotone {I J K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (b : HilbertBasis I ℂ H) (d : HilbertBasis J ℂ K)
    (alpha : ℝ≥0∞) (halpha : (1 / 2 : ℝ≥0∞) ≤ alpha)
    (rho sigma : H →L[ℂ] H) (hrho : IsPositive rho) (hsigma : IsPositive sigma)
    (htrho : IsTraceClass rho) (htsigma : IsTraceClass sigma)
    (hnonzero : 0 < (operatorTrace b rho).re)
    (Phi : (H →L[ℂ] H) → (K →L[ℂ] K))
    (hPhi : QAlgorithms.Papers.Independent.Support50.P20.IsHilbertCPTP b d Phi) :
    traceNormalizedHilbertRenyi d alpha (Phi rho, Phi sigma) ≤
      traceNormalizedHilbertRenyi b alpha (rho, sigma) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P48

end
