-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P48_renyiDivergence_jointConvexity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P48.renyiDivergence_jointConvexity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:56:56.331475+00:00
-- url     : https://prove2.me/theorems/e9e06ced-f1e0-46ff-ba83-178eb14ce1aa
-- title:
--   Joint convexity of the sandwiched entropy on a fixed-trace slice
-- statement:
--   Fix a complex Hilbert space, a real order $1/2\le\alpha\le1$, and a finite real number $t>0$. Let $(\rho_1,\sigma_1)$ and $(\rho_2,\sigma_2)$ be pairs of nonnegative trace-class operators with $\operatorname{Tr}\rho_1=\operatorname{Tr}\rho_2=t$. For every $\lambda\in[0,1]$, put $\rho_\lambda=\lambda\rho_1+(1-\lambda)\rho_2$ and $\sigma_\lambda=\lambda\sigma_1+(1-\lambda)\sigma_2$. Then
--
--   $$D_\alpha(\rho_\lambda\Vert\sigma_\lambda)\le\lambda D_\alpha(\rho_1\Vert\sigma_1)+(1-\lambda)D_\alpha(\rho_2\Vert\sigma_2).$$
--
--   The divergence is the trace-normalized sandwiched entropy in natural logarithms, with its extended Umegaki value at $\alpha=1$. The second arguments may vanish; support inclusion is not required. On this domain the divergences are finite real numbers or positive infinity, and the endpoint weights have their exact Jensen interpretation.
--
--   The common trace is fixed over the entire slice, not restricted to the density-matrix value one.
-- source:
--   Monotonicity of a relative Rényi entropy, arXiv:1306.5358v3, PDF p. 2, Theorem 2 (Joint convexity)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P48

noncomputable section

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Bridge50.P48

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsPositive IsTraceClass operatorTrace)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Frank--Lieb, PDF p.2, Theorem 2; proof on PDF p.3.
The common positive trace t is fixed for the whole slice, and alpha=1 is included. -/
theorem renyiDivergence_jointConvexity {I : Type*} (b : HilbertBasis I ℂ H)
    (t : ℝ) (ht : 0 < t) (alpha : ℝ) (halpha : (1 / 2 : ℝ) ≤ alpha ∧ alpha ≤ 1) :
    entropyJointConvexOn (traceSlice b t) (traceNormalizedHilbertRenyi b (ENNReal.ofReal alpha)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P48

end
