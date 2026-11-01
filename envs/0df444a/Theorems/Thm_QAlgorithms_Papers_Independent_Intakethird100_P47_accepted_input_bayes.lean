-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P47_accepted_input_bayes
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P47.accepted_input_bayes
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:34:56.326436+00:00
-- url     : https://prove2.me/theorems/c6257748-f32a-47c8-b0ba-fb066ca93a2e
-- title:
--   Bayes identities for accepted inputs
-- statement:
--   Let $p(a,b\mid A,B)$ be a nonnegative binary conditional distribution normalized for each pair of settings, and let $w(A,B)$ be a nonnegative normalized input law. The joint law is $w(A,B)p(a,b\mid A,B)$. Set $S=\{a=b=0\}$, $s=\sum_{A,B}w(A,B)p(00\mid A,B)$, and, when $s>0$, let $J(A,B)=w(A,B)p(00\mid A,B)/s$ be the accepted setting law.
--
--   Assume $s>0$. Define
--   $$
--   \sigma=w(00)p(00\mid00)+w(01)p(00\mid01),\qquad
--   \nu=w(10)p(00\mid10)+w(11)p(00\mid11).
--   $$
--   Then $s=\sigma+\nu$ and
--   $$
--   \Pr[A=0\mid S]=\frac{\sigma}{\sigma+\nu},\qquad
--   \Pr[A=1\mid S]=\frac{\nu}{\sigma+\nu}.
--   $$
--   These identities separate the observed input law from the conditional behavior and fix the conditioning used in subsequent scalar calculations.
-- source:
--   Device-independent quantum key distribution based on measurement inputs, arXiv:1308.6447v3, PDF p. 6, IV C: accepted-input Bayes identities (14)–(15)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

namespace QAlgorithms.Papers.Independent.Intakethird100.P47

open scoped ComplexConjugate

open scoped BigOperators

/-- IV C, PDF p.6, (14)–(15): Bayes identities with a positive acceptance probability.
Direct inspection of PDF p.6 confirms (15b) already prints the correct (1,1) second term;
the plan's claim that it repeats (0,1) is erroneous. No source correction is made here. -/
theorem accepted_input_bayes (p : Behavior) (w : PairLaw)
    (hp : IsBehavior p) (hw : IsPairLaw w) (hs : 0 < siftingProbability p w) :
    siftingProbability p w = aliceMass p w false + aliceMass p w true ∧
    aliceMass p w false =
      p false false false false * w false false + p false true false false * w false true ∧
    aliceMass p w true =
      p true false false false * w true false + p true true false false * w true true ∧
    aliceMarginal (acceptedLaw p w) false =
      aliceMass p w false / (aliceMass p w false + aliceMass p w true) ∧
    aliceMarginal (acceptedLaw p w) true =
      aliceMass p w true / (aliceMass p w false + aliceMass p w true) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P47
