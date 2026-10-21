-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P02_example_7_1
-- name    : QAlgorithms.Papers.Independent.Claimed50.P02.example_7_1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:32:21.924892+00:00
-- url     : https://prove2.me/theorems/7f4b3f71-43df-44eb-b434-caa18aa74a69
-- title:
--   Example 7.1: exact n=3 qubit principal-eigenvalue success curve
-- statement:
--   Consider deciding whether the largest eigenvalue of a random qubit state is below a threshold $c\in[1/2,1]$, from $n$ copies. The state is obtained by tracing one qubit out of a Haar-uniform two-qubit pure state. Its largest eigenvalue $t$ has probability density $6(2t-1)^2$ on $[1/2,1]$. Choose one two-outcome POVM before the unknown eigenbasis; maximize its worst-case-over-basis success averaged over this eigenvalue law. Denote this attained optimum by $p_n(c)$.
--
--   Let $c_1,c_2$ be the unique roots, respectively in $(0.8215,0.8216)$ and $(0.9138,0.9139)$, of
--   $$96x^5-240x^4+200x^3-60x^2+3,\qquad 24x^5-60x^4+70x^3-45x^2+15x-3.$$
--   Then
--   $$
--   p_3(c)=\begin{cases}
--   2(1-c)(4c^2-2c+1),&1/2\le c\le c_1,\\
--   7/5-(6/5)c(16c^4-40c^3+40c^2-20c+5),&c_1\le c\le c_2,\\
--   (2c-1)^3,&c_2\le c\le1.
--   \end{cases}
--   $$
--   The branches agree at their shared endpoints, and $p_3(1/2)=p_3(1)=1$. Throughout the interval, $p_3(c)\ge p_3(c_2)$ and $p_3(c)\ge p_1(c)$, where
--   $$p_1(c)=\max\{2(1-c)(4c^2-2c+1),(2c-1)^3\}.$$
--   The minimum of $p_1$ is $1/2$, attained at $c=1/2+2^{-4/3}$. This is an exact success curve; the decimal values in the source merely locate algebraic breakpoints and the minimum.
-- source:
--   Linear programming with unitary-equivariant constraints, arXiv:2207.05713v2, PDF p. 39, Example 7.1: exact n=3 qubit principal-eigenvalue success curve

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P02

namespace QAlgorithms.Papers.Independent.Claimed50.P02

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P69 (Sites choi)

noncomputable section

/-- Paper p.39, Example 7.1, Eqs.(152),(153): the exact operational optimum,
breakpoint isolation, endpoint values, global minimum and one-copy comparison.
Eq.(150)'s printed min_U max_PQ is corrected to max_PQ min_U, as required by
the fixed-measurement problem and the subsequent twirling argument. Decimal
approximations are locators only. Real rpow represents 2^(-4/3). -/
theorem example_7_1 :
    (firstBreakpoint ∈ Set.Ioo (8215/10000 : ℝ) (8216/10000 : ℝ) ∧
      firstBreakpointPolynomial firstBreakpoint = 0 ∧
      ∀ x ∈ Set.Ioo (8215/10000 : ℝ) (8216/10000 : ℝ),
        firstBreakpointPolynomial x = 0 → x = firstBreakpoint) ∧
    (secondBreakpoint ∈ Set.Ioo (9138/10000 : ℝ) (9139/10000 : ℝ) ∧
      secondBreakpointPolynomial secondBreakpoint = 0 ∧
      ∀ x ∈ Set.Ioo (9138/10000 : ℝ) (9139/10000 : ℝ),
        secondBreakpointPolynomial x = 0 → x = secondBreakpoint) ∧
    (∀ c ∈ Set.Icc (1/2 : ℝ) 1,
      IsGreatest (qubitThresholdGuarantees 3 c) (threeCopySuccessCurve c) ∧
      threeCopySuccessCurve secondBreakpoint ≤ threeCopySuccessCurve c ∧
      oneCopySuccessCurve c ≤ threeCopySuccessCurve c ∧
      IsGreatest (qubitThresholdGuarantees 1 c) (oneCopySuccessCurve c)) ∧
    threeCopySuccessCurve (1/2) = 1 ∧ threeCopySuccessCurve 1 = 1 ∧
    IsLeast (oneCopySuccessCurve '' Set.Icc (1/2 : ℝ) 1) (1/2 : ℝ) ∧
    oneCopySuccessCurve (1/2 + Real.rpow 2 (-4/3 : ℝ)) = 1/2 ∧
    2*(1-firstBreakpoint)*(4*firstBreakpoint^2-2*firstBreakpoint+1) =
      7/5-(6/5)*firstBreakpoint*(16*firstBreakpoint^4-40*firstBreakpoint^3+
        40*firstBreakpoint^2-20*firstBreakpoint+5) ∧
    7/5-(6/5)*secondBreakpoint*(16*secondBreakpoint^4-40*secondBreakpoint^3+
      40*secondBreakpoint^2-20*secondBreakpoint+5) = (2*secondBreakpoint-1)^3 := by sorry

end

end QAlgorithms.Papers.Independent.Claimed50.P02
