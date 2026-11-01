-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P47_hardy_ratio_reduction
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P47.hardy_ratio_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:35:55.513213+00:00
-- url     : https://prove2.me/theorems/b8309331-eb76-4eca-a619-94aa6f42152c
-- title:
--   Scalar monotonicity at fixed Hardy statistics
-- statement:
--   Let $p(a,b\mid A,B)$ be a nonnegative binary conditional distribution normalized for each pair of settings, and let $w(A,B)$ be a nonnegative normalized input law. The joint law is $w(A,B)p(a,b\mid A,B)$. Set $S=\{a=b=0\}$, $s=\sum_{A,B}w(A,B)p(00\mid A,B)$, and, when $s>0$, let $J(A,B)=w(A,B)p(00\mid A,B)/s$ be the accepted setting law.
--
--   Assume $w$ has full support, $h=H(p)$ where $H(p)=(p(00\mid00),-p(00\mid10),-p(00\mid01),-p(11\mid11))$, $h_1>0$, and $\sigma=\sum_Bw(0,B)p(00\mid0,B)>0$. Then
--   $$
--   \sigma=h_1w(00)-h_3w(01).
--   $$
--   Every other normalized nonnegative behavior $p'$ with $H(p')=h$ has the same $\sigma$ and positive acceptance. Write $\nu=\sum_Bw(1,B)p(00\mid1,B)$ and similarly $\nu'$ for $p'$. Then
--   $$
--   \Pr_p[A=0\mid S]\le\Pr_{p'}[A=0\mid S]\iff \nu'\le\nu,
--   $$
--   $$
--   \Pr_p[A=1\mid S]\le\Pr_{p'}[A=1\mid S]\iff \nu\le\nu'.
--   $$
--   Thus a feasible minimum of $\nu$ maximizes the first ratio and a feasible maximum maximizes the second. No existence or numerical certification of such endpoints is asserted.
-- source:
--   Device-independent quantum key distribution based on measurement inputs, arXiv:1308.6447v3, PDF p. 7, V: scalar reduction for Hardy conditional ratios

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

namespace QAlgorithms.Papers.Independent.Intakethird100.P47

open scoped ComplexConjugate

open scoped BigOperators

/-- V, PDF p.7, using (12),(14)–(15) on pp.5–6: fixed Hardy data fix sigma.
The conditional zero ratio decreases with nu and the one ratio increases with nu.
Endpoints maximize the respective ratios when feasible endpoints exist; none are assumed attained. -/
theorem hardy_ratio_reduction (p : Behavior) (w : PairLaw)
    (hp : IsBehavior p) (hw : IsPairLaw w) (hwpos : ∀ A B, 0 < w A B)
    (hh1 : 0 < hardyStatistics p 0)
    (hsigma : 0 < aliceMass p w false) :
    aliceMass p w false = hardyStatistics p 0 * w false false -
      hardyStatistics p 2 * w false true ∧
    ∀ p2 : Behavior, IsBehavior p2 → hardyStatistics p2 = hardyStatistics p →
      aliceMass p2 w false = aliceMass p w false ∧
      0 < siftingProbability p2 w ∧
      (aliceMarginal (acceptedLaw p w) false ≤ aliceMarginal (acceptedLaw p2 w) false ↔
        aliceMass p2 w true ≤ aliceMass p w true) ∧
      (aliceMarginal (acceptedLaw p w) true ≤ aliceMarginal (acceptedLaw p2 w) true ↔
        aliceMass p w true ≤ aliceMass p2 w true) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P47
