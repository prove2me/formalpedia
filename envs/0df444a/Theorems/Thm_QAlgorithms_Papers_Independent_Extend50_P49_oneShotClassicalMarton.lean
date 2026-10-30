-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P49_oneShotClassicalMarton
-- name    : QAlgorithms.Papers.Independent.Extend50.P49.oneShotClassicalMarton
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:22:15.895981+00:00
-- url     : https://prove2.me/theorems/e9f40b5f-2d2c-4f62-852f-7c49215171f1
-- title:
--   One-shot classical Marton inner bound
-- statement:
--   Let $X,U,V,Y,Z$ be finite alphabets, $W(y,z\mid x)$ a normalized classical broadcast transition law, $p_{UV}$ a normalized auxiliary joint law, and $f:U\times V\to X$ a deterministic function. Compute the joint distribution $p(u,v,y,z)=p_{UV}(u,v)W(y,z\mid f(u,v))$, including its $UY$ and $VZ$ marginals. For positive integers $M_i$ set $R_i=\log_2M_i$. Let $0\le\varepsilon\le1$, $0\le\varepsilon_\infty\le1/4$, $0\le\varepsilon_0<1$ and $t>0$. Put $a=I_0^{\varepsilon_0}(U;Y)$, $b=I_0^{\varepsilon_0}(V;Z)$ and $c=I_\infty^{\varepsilon_\infty}(U;V)$. Here the classical $I_0^{\varepsilon_0}(A;D)$ is the supremum of $-\log_2\sum_{(a,d)\in G}p_A(a)p_D(d)$ over sets with $p_{AD}(G)\ge1-\varepsilon_0$; the inequality is NON-STRICT. The smooth maximum uses STRICT retained mass and the original product marginals, as in Definition 4. Extrema and zero logarithms have extended values.
--   If
--   $$\begin{aligned}R_1&\le a-5\log_2(1/t)-2,\\R_2&\le b-5\log_2(1/t)-2,\\R_1+R_2&\le a+b-c-11\log_2(1/t)-5,\\37t+8\varepsilon_0&\le\varepsilon,\end{aligned}$$
--   then there exist fixed deterministic maps $F:[M_1]\times[M_2]\to X$, $D_1:Y\to[M_1]$, and $D_2:Z\to[M_2]$ such that
--   $$\Pr\{D_1(Y)\ne M_1\ \text{or}\ D_2(Z)\ne M_2\}\le\varepsilon.$$
--   In this probability the messages are independent and uniform, and the output law conditional on them is $W(\cdot,\cdot\mid F(M_1,M_2))$. This is a one-use, two-private-message coding result with average joint error. The classical endpoint $\varepsilon_0=0$ remains included.
-- source:
--   One-shot Marton inner bound for classical-quantum broadcast channel, arXiv:1410.3248v5, PDF p. 3, Theorem 4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P49

open QAlgorithms MeasureTheory Filter

open scoped BigOperators Matrix ComplexOrder Topology

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 4, PDF p.3, proof pp.11-14: one-shot classical Marton bound.
The Definition 7 endpoint epsilon0=0 is retained; the error budget is 37,8. -/
theorem oneShotClassicalMarton {X U V Y Z : Type}
    [Fintype X] [Fintype U] [Fintype V] [Fintype Y] [Fintype Z]
    (N : ClassicalBroadcastChannel X Y Z) (p : AuxiliaryLaw (U × V)) (f : U → V → X)
    (M1 M2 : ℕ) (hM1 : 0 < M1) (hM2 : 0 < M2)
    (epsilon epsilonInfinity epsilon0 tildeEpsilon : ℝ)
    (hEpsilon : 0 ≤ epsilon ∧ epsilon ≤ 1)
    (hInfinity : 0 ≤ epsilonInfinity ∧ epsilonInfinity ≤ 1 / 4)
    (hZero : 0 ≤ epsilon0 ∧ epsilon0 < 1) (hTilde : 0 < tildeEpsilon)
    (hBudget : 37 * tildeEpsilon + 8 * epsilon0 ≤ epsilon)
    (hRates : MartonConstraints (smoothClassicalMin (inducedUY N p f) epsilon0)
      (smoothClassicalMin (inducedVZ N p f) epsilon0)
      (strictSmoothMaxInformation p.prob epsilonInfinity) M1 M2 tildeEpsilon) :
    ∃ D : PrivateClassicalCode X Y Z M1 M2, classicalError N D ≤ epsilon := by sorry

end QAlgorithms.Papers.Independent.Extend50.P49

end
