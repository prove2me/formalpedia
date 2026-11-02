-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P91_swivelMonotonicity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P91.swivelMonotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:20:20.610805+00:00
-- url     : https://prove2.me/theorems/fa8ee3bd-3e74-4345-b6b9-7075bcd0ab8a
-- title:
--   Commuting unitary swivels make the powered Schatten objective nonincreasing
-- statement:
--   Let $d,L\ge1$ be integers and let $C_1,\ldots,C_L$ act on the common space $\mathbb C^d$, with products in the displayed order. For $1\le r<\infty$, write $\|X\|_r=(\operatorname{Tr}(X^*X)^{r/2})^{1/r}$ for the unnormalized Schatten norm. On a positive eigenvalue $\lambda$, $C^z$ acts by $\exp(z\log\lambda)$, and it acts by zero on the kernel. No commutation between different factors or trace normalization is assumed.
--
--   Assume every $C_i$ is positive semidefinite. Let $\mathcal V_C$ be the set of all tuples of full-space unitaries $(V_1,\ldots,V_L)$ satisfying $V_iC_i=C_iV_i$ for every $i$. For every pair of finite real exponents $1\le q\le p$, both displayed maxima are attained and
--
--   $$
--   \max_{V\in\mathcal V_C}\left\|C_1^{1/p}V_1\cdots C_L^{1/p}V_L\right\|_p^p
--   \le
--   \max_{W\in\mathcal V_C}\left\|C_1^{1/q}W_1\cdots C_L^{1/q}W_L\right\|_q^q.
--   $$
--
--   This is the monotonicity of the optimized powered norm, including singular and zero factors.
--
--   **Formalization Note** The theorem asserts greatest elements of the two explicitly constructed sets of objective values and compares them. Greatest-element membership records attainment; there is no default real supremum.
-- source:
--   Monotonicity of $p$-norms of multiple operators via unitary swivels, arXiv:1610.01262v1, PDF p. 3, Theorem 1, Eq.(5); abstract p.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P91

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakethird100.P91

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Dependency50.P21
  (extendedLog upperLogIntegral betaDensity betaZero interpolationExponent)

open QAlgorithms.Papers.Independent.Bridge50.P29
  (positiveComplexPower orderedProduct)

/-- Theorem 1, Eq.(5), arXiv:1610.01262v1, PDF p.3 (abstract p.1).
For every finite real 1 <= q <= p, both maxima are attained and the
p-objective is at most the q-objective. IsGreatest includes attainment,
so this states literal maxima, rather than an unattained supremum bound.
The dimension and sequence are nonzero; matrices may be singular or zero
and need not have trace one. Positive powers use the support-zero convention. -/
theorem swivelMonotonicity
    (d L : ℕ) (hd : 0 < d) (hL : 0 < L)
    (C : Fin L → Matrix (Fin d) (Fin d) ℂ)
    (hC : ∀ i, (C i).PosSemidef)
    (p q : ℝ) (hq : 1 ≤ q) (hqp : q ≤ p) :
    ∃ mp mq : ℝ,
      IsGreatest (swivelValues C p) mp ∧
      IsGreatest (swivelValues C q) mq ∧ mp ≤ mq := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P91

end
