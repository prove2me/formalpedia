-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P91_traceExponentialInequality
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P91.traceExponentialInequality
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:22:02.37074+00:00
-- url     : https://prove2.me/theorems/5a8f2435-272c-4de9-bc8a-a613629a5174
-- title:
--   Multioperator trace-exponential inequality
-- statement:
--   Let $d,L\ge1$ be integers and let $C_1,\ldots,C_L$ act on the common space $\mathbb C^d$, with products in the displayed order. For $1\le r<\infty$, write $\|X\|_r=(\operatorname{Tr}(X^*X)^{r/2})^{1/r}$ for the unnormalized Schatten norm. On a positive eigenvalue $\lambda$, $C^z$ acts by $\exp(z\log\lambda)$, and it acts by zero on the kernel. No commutation between different factors or trace normalization is assumed.
--
--   Assume every $C_i$ is positive definite, let $q\ge1$ be finite and real, and put $\beta_0(t)=\pi/(2[\cosh(\pi t)+1])$. The matrix logarithms are the self-adjoint spectral natural logarithms and $\exp$ is the matrix exponential. Then
--
--   $$
--   \log\operatorname{Tr}\exp\!\left(\sum_{j=1}^{L}\log C_j\right)
--   \le\int_{\mathbb R}\beta_0(t)
--   \log\left(\left\|C_1^{(1+it)/q}\cdots C_L^{(1+it)/q}\right\|_q^q\right)\,dt.
--   $$
--
--   All displayed logarithms are finite; the weighted integrand is integrable. This is the trace-exponential consequence of multioperator interpolation in the positive definite setting.
--
--   **Formalization Note** The real part of the complex matrix trace is used on the left; for the exponential of the self-adjoint sum this trace is real and positive.
-- source:
--   Monotonicity of $p$-norms of multiple operators via unitary swivels, arXiv:1610.01262v1, PDF p. 4, Corollary 3, Eq.(22)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P91

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakethird100.P91

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Dependency50.P21
  (extendedLog upperLogIntegral betaDensity betaZero interpolationExponent)

open QAlgorithms.Papers.Independent.Bridge50.P29
  (positiveComplexPower orderedProduct)

/-- Corollary 3, Eq.(22), arXiv:1610.01262v1, PDF p.4.
The C_i are positive DEFINITE as printed in this numbered corollary.
The left side is the log of the trace of the exponential of the SUM of
spectral natural logarithms. The right side uses beta_0 and the q-th
power inside the log. Positive definiteness makes all these logs finite;
no Lie--Trotter identity or integrability conclusion is assumed. -/
theorem traceExponentialInequality
    (d L : ℕ) (hd : 0 < d) (hL : 0 < L)
    (C : Fin L → Matrix (Fin d) (Fin d) ℂ)
    (hC : ∀ i, (C i).PosDef)
    (q : ℝ) (hq : 1 ≤ q) :
    extendedLog ((NormedSpace.exp (∑ i, cfc Real.log (C i))).trace.re) ≤
    upperLogIntegral (fun t =>
      (betaZero t : EReal) *
        extendedLog ((schattenNorm (ENNReal.ofReal q)
          (orderedProduct (fun i => positiveComplexPower (C i)
            ((1 + (t : ℂ) * Complex.I) / (q : ℂ))))) ^ q)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P91

end
