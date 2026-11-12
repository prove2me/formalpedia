-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P47_ideal_uniform_dropping
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P47.ideal_uniform_dropping
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T05:36:56.388501+00:00
-- url     : https://prove2.me/theorems/95a9b98b-a95d-4abb-8dc8-2aa2177eb1ce
-- title:
--   Ideal uniform-input balance and retained yield
-- statement:
--   Let $p(a,b\mid A,B)$ be a nonnegative binary conditional distribution normalized for each pair of settings, and let $w(A,B)$ be a nonnegative normalized input law. The joint law is $w(A,B)p(a,b\mid A,B)$. Set $S=\{a=b=0\}$, $s=\sum_{A,B}w(A,B)p(00\mid A,B)$, and, when $s>0$, let $J(A,B)=w(A,B)p(00\mid A,B)/s$ be the accepted setting law.
--
--   Suppose $w(A,B)=1/4$, $p(00\mid00)=x=(5\sqrt5-11)/2$, $p(00\mid11)=y=\sqrt5-2$, and the two cross-setting acceptance probabilities vanish. Keep every accepted $A=0$ run and independently keep each accepted $A=1$ run with probability $x/y\in(0,1]$. Then
--   $$
--   s=\frac{x+y}{4}>0,\qquad \Pr[\mathrm{keep}\mid S]=\frac{2x}{x+y},\qquad
--   \Pr[S\text{ and keep}]=\frac{5\sqrt5-11}{4}.
--   $$
--   In the retained law Alice's two bit values each have probability $1/2$, Alice and Bob agree with probability one, and the larger marginal probability is $1/2$.
--
--   These are population probabilities and a raw retained yield. Marginal balance alone does not establish Eve's optimal guessing probability or an operational secure key rate.
-- source:
--   Device-independent quantum key distribution based on measurement inputs, arXiv:1308.6447v3, PDF p. 8, VII B.1: ideal uniform-input balance and retained yield

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

namespace QAlgorithms.Papers.Independent.Intakethird100.P47

open scoped ComplexConjugate

open scoped BigOperators

/-- VII B.1, PDF pp.8–9: ideal uniform-input dropping balances the accepted bits,
preserves agreement, and keeps an exact fraction (5 sqrt(5)-11)/4 of all runs.
The half guessing probability is marginal guessing without side information; secure key
rate and Eve's optimal transcript-dependent guessing remain deferred separately. -/
theorem ideal_uniform_dropping (p : Behavior) (hp : IsBehavior p)
    (h00 : p false false false false = (5 * Real.sqrt 5 - 11) / 2)
    (h11 : p true true false false = Real.sqrt 5 - 2)
    (h10 : p true false false false = 0) (h01 : p false true false false = 0) :
    let x := (5 * Real.sqrt 5 - 11) / 2
    let y := Real.sqrt 5 - 2
    let w := binarySettingLaw (1 / 2) (1 / 2)
    let j := acceptedLaw p w
    let k : Bool → ℝ := fun A => if A then x / y else 1
    0 < siftingProbability p w ∧ 0 < x / y ∧ x / y ≤ 1 ∧
    siftingProbability p w = (x + y) / 4 ∧
    retention j k = 2 * x / (x + y) ∧
    siftingProbability p w * retention j k = (5 * Real.sqrt 5 - 11) / 4 ∧
    (∀ A, aliceMarginal (retainedLaw j k) A = 1 / 2) ∧
    (∑ A, retainedLaw j k A A) = 1 ∧
    max (aliceMarginal (retainedLaw j k) false)
      (aliceMarginal (retainedLaw j k) true) = 1 / 2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P47
