-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P49_oneShotCqMarton
-- name    : QAlgorithms.Papers.Independent.Extend50.P49.oneShotCqMarton
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:21:07.390305+00:00
-- url     : https://prove2.me/theorems/b97c09a6-0de7-449a-8850-15d8685cecd0
-- title:
--   One-shot classical-quantum Marton inner bound
-- statement:
--   Let $X,U,V$ be finite alphabets and let $B,C$ be arbitrary nonzero finite-dimensional quantum systems. A classical-quantum broadcast channel maps $x\in X$ to a positive trace-one joint density operator $\rho_x^{BC}$. Fix a normalized joint law $p_{UV}$ and a deterministic map $f:U\times V\to X$, and compute
--   $$\rho^{UVBC}=\sum_{u,v}p_{UV}(u,v)|u\rangle\langle u|\otimes|v\rangle\langle v|\otimes\rho_{f(u,v)}^{BC}.$$
--   All marginals below are the actual partial traces of this state. Let $M_1,M_2$ be positive integers and set $R_i=\log_2M_i$. Let $0\le\varepsilon\le1$, $0\le\varepsilon_\infty\le1/4$, $0\le\varepsilon_0<1$, and $t>0$. Write $a=I_0^{\varepsilon_0}(U;B)$, $b=I_0^{\varepsilon_0}(V;C)$ and $c=I_\infty^{\varepsilon_\infty}(U;V)$. The quantum smooth minimum is the supremum of $-\log_2\operatorname{Tr}[\Gamma(\rho^U\otimes\rho^B)]$ over effects $0\le\Gamma\le I$ with STRICT acceptance $\operatorname{Tr}(\Gamma\rho^{UB})>1-\varepsilon_0$, and similarly for $V,C$. The smooth maximum is the infimum over subsets of joint mass STRICTLY greater than $1-\varepsilon_\infty$ of the largest log likelihood ratio against the original product marginals. These are extended extrema, with $\log_2 0=-\infty$.
--   If
--   $$\begin{aligned}R_1&\le a-5\log_2(1/t)-2,\\R_2&\le b-5\log_2(1/t)-2,\\R_1+R_2&\le a+b-c-11\log_2(1/t)-5,\\40t+16\varepsilon_0&\le\varepsilon,\end{aligned}$$
--   then there exist a fixed deterministic encoder $F:[M_1]\times[M_2]\to X$ and separate fixed local decoding POVMs $T^B,T^C$ satisfying
--   $$\frac1{M_1M_2}\sum_{m_1,m_2}\left(1-\operatorname{Tr}[(T^B_{m_1}\otimes T^C_{m_2})\rho_{F(m_1,m_2)}^{BC}]\right)\le\varepsilon.$$
--   This is one-shot transmission of two independent uniform private classical messages, with average probability that either intended message is wrong and with no common message, feedback, or entanglement assistance.
-- source:
--   One-shot Marton inner bound for classical-quantum broadcast channel, arXiv:1410.3248v5, PDF p. 3, Theorem 3

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P49

open QAlgorithms MeasureTheory Filter

open scoped BigOperators Matrix ComplexOrder Topology

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 3, PDF p.3, proof pp.6-10: one-shot cq Marton bound with all three
rate constraints and the 40,16 error budget. The code is chosen before the messages. -/
theorem oneShotCqMarton {X U V B C : Type}
    [Fintype X] [Fintype U] [Fintype V] [Fintype B] [Fintype C]
    (N : CqChannel X B C) (p : AuxiliaryLaw (U × V)) (f : U → V → X)
    (M1 M2 : ℕ) (hM1 : 0 < M1) (hM2 : 0 < M2)
    (epsilon epsilonInfinity epsilon0 tildeEpsilon : ℝ)
    (hEpsilon : 0 ≤ epsilon ∧ epsilon ≤ 1)
    (hInfinity : 0 ≤ epsilonInfinity ∧ epsilonInfinity ≤ 1 / 4)
    (hZero : 0 ≤ epsilon0 ∧ epsilon0 < 1) (hTilde : 0 < tildeEpsilon)
    (hBudget : 40 * tildeEpsilon + 16 * epsilon0 ≤ epsilon)
    (hRates : MartonConstraints (smoothQuantumMin (inducedUB N p f) epsilon0)
      (smoothQuantumMin (inducedVC N p f) epsilon0)
      (strictSmoothMaxInformation p.prob epsilonInfinity) M1 M2 tildeEpsilon) :
    ∃ D : CqCode X B C M1 M2, cqJointError N D ≤ epsilon := by sorry

end QAlgorithms.Papers.Independent.Extend50.P49

end
