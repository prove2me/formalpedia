-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P47_balanced_input_bias_and_yield
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P47.balanced_input_bias_and_yield
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:37:27.893832+00:00
-- url     : https://prove2.me/theorems/08e10df1-cb17-41e9-98af-a33fafde95ac
-- title:
--   Balancing local setting bias and exact accepted yield
-- statement:
--   Let $p(a,b\mid A,B)$ be a nonnegative binary conditional distribution normalized for each pair of settings, and let $w(A,B)$ be a nonnegative normalized input law. The joint law is $w(A,B)p(a,b\mid A,B)$. Set $S=\{a=b=0\}$, $s=\sum_{A,B}w(A,B)p(00\mid A,B)$, and, when $s>0$, let $J(A,B)=w(A,B)p(00\mid A,B)/s$ be the accepted setting law.
--
--   Let $x=p(00\mid00)>0$, $y=p(00\mid11)>0$, and assume both cross-setting acceptance probabilities vanish. Choose independent settings with $\Pr[A=0]=\Pr[B=0]=r\in[0,1]$. Acceptance has positive probability even at the endpoints. With $r_b=\sqrt y/(\sqrt x+\sqrt y)\in(0,1)$,
--   $$
--   \bigl(\forall k,\ \Pr[A=k\mid S]=\tfrac12\bigr)
--   \iff xr^2=y(1-r)^2\iff r=r_b.
--   $$
--   At this balancing bias,
--   $$
--   s=2xr^2=\frac{2xy}{(\sqrt x+\sqrt y)^2}.
--   $$
--   For $x=(5\sqrt5-11)/2$ and $y=\sqrt5-2$, $r_b=(\sqrt5-1)/2$. This balances the raw key values and evaluates acceptance; it does not maximize a specified cryptographic rate.
-- source:
--   Device-independent quantum key distribution based on measurement inputs, arXiv:1308.6447v3, PDF p. 9, VII B.2: balancing input distribution and exact ideal yield

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

namespace QAlgorithms.Papers.Independent.Intakethird100.P47

open scoped ComplexConjugate

open scoped BigOperators

/-- VII B.2, PDF p.9, (19a,b): the unique equal local input bias balancing the ideal
accepted settings, with exact yield. The denominator is (sqrt(x)+sqrt(y)) squared.
The yield is a raw accepted-run probability, not an operational secrecy capacity. -/
theorem balanced_input_bias_and_yield (p : Behavior) (hp : IsBehavior p)
    (x y r : ℝ) (hx : 0 < x) (hy : 0 < y) (hr : 0 ≤ r ∧ r ≤ 1)
    (h00 : p false false false false = x) (h11 : p true true false false = y)
    (h10 : p true false false false = 0) (h01 : p false true false false = 0) :
    let w := binarySettingLaw r r
    let rb := Real.sqrt y / (Real.sqrt x + Real.sqrt y)
    0 < siftingProbability p w ∧ 0 < rb ∧ rb < 1 ∧
    ((∀ A, aliceMarginal (acceptedLaw p w) A = 1 / 2) ↔ x * r ^ 2 = y * (1 - r) ^ 2) ∧
    (x * r ^ 2 = y * (1 - r) ^ 2 ↔ r = rb) ∧
    (r = rb → siftingProbability p w = 2 * x * r ^ 2 ∧
      siftingProbability p w = 2 * x * y / (Real.sqrt x + Real.sqrt y) ^ 2) ∧
    (x = (5 * Real.sqrt 5 - 11) / 2 → y = Real.sqrt 5 - 2 →
      rb = (Real.sqrt 5 - 1) / 2) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P47
