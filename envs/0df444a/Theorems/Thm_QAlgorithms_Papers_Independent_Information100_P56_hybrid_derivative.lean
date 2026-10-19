-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_hybrid_derivative
-- name    : QAlgorithms.Papers.Independent.Information100.P56.hybrid_derivative
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:24:31.694618+00:00
-- url     : https://prove2.me/theorems/761b1cf5-d706-4be9-840a-a264e91bd04e
-- title:
--   Section VI C, Eq.(54): derivative of the hybrid entropy difference
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. In the hybrid binary channel, Bob has the binary symmetric channel of crossover $q$, while Eve receives $|\psi_b\rangle=\sqrt{q^{\prime}}|0\rangle+(-1)^b\sqrt{1-q^{\prime}}|1\rangle$. Here $q,q^{\prime}\in[0,1]$, and $x$ is the probability of input symbol $1$. Write $h$ for natural binary entropy. Suppose $0<x<1/2$ and $0<q^{\prime}<1$. Write $a=x(1-q)+(1-x)q$ and $s=\sqrt{1-16q^{\prime}(1-q^{\prime})x(1-x)}$. Then
--
--   $$\frac{d\Delta}{dx}=(1-2q)\log\frac{1-a}{a}-\frac{4q^{\prime}(1-q^{\prime})(1-2x)}s\log\frac{1+s}{1-s}.$$
--
--   The strict domain makes $a\in(0,1)$ and $s\in(0,1)$, so all displayed denominators and logarithms have their intended meanings. This is the derivative used for stationary points.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 15, Section VI C, Eq.(54): derivative of the hybrid entropy difference

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Section VI C, p.15, Eq.(54): the derivative in the nonconstant interior regime.
Here s is the square root; its radical is displaced by text extraction. -/
theorem hybrid_derivative (q qprime x : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hqp : 0 < qprime ∧ qprime < 1)
    (hx : 0 < x ∧ x < 1 / 2) :
    let a := binaryConvolution x q
    let s := Real.sqrt (1 - 16 * qprime * (1 - qprime) * x * (1 - x))
    HasDerivAt (hybridFormula q qprime)
      ((1 - 2 * q) * Real.log ((1 - a) / a) -
        4 * qprime * (1 - qprime) * (1 - 2 * x) / s * Real.log ((1 + s) / (1 - s))) x := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
