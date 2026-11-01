-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P47_accepted_settings_agree
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P47.accepted_settings_agree
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:32:41.589461+00:00
-- url     : https://prove2.me/theorems/fc8c759f-6ed0-4f00-aaee-6c34e5ccc185
-- title:
--   Accepted Hardy settings agree
-- statement:
--   Let $p(a,b\mid A,B)$ be a nonnegative binary conditional distribution normalized for each pair of settings, and let $w(A,B)$ be a nonnegative normalized input law. The joint law is $w(A,B)p(a,b\mid A,B)$. Set $S=\{a=b=0\}$, $s=\sum_{A,B}w(A,B)p(00\mid A,B)$, and, when $s>0$, let $J(A,B)=w(A,B)p(00\mid A,B)/s$ be the accepted setting law.
--
--   Assume $s>0$ and the two cross-setting zero constraints $p(00\mid10)=p(00\mid01)=0$. Every unequal setting pair has zero joint acceptance mass, and
--   $$
--   \Pr[A=B\mid S]=\sum_{A=B}J(A,B)=1.
--   $$
--   This gives perfect agreement of the raw setting bits under the ideal cross-setting constraints.
-- source:
--   Device-independent quantum key distribution based on measurement inputs, arXiv:1308.6447v3, PDF p. 3, II B: perfect correlation of accepted settings

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

namespace QAlgorithms.Papers.Independent.Intakethird100.P47

open scoped ComplexConjugate

open scoped BigOperators

/-- II B, PDF p.3, using (1) on p.2: accepted settings agree with probability one.
No restriction to qubits, uniform inputs or a claim of secrecy is involved. -/
theorem accepted_settings_agree (p : Behavior) (w : PairLaw)
    (hp : IsBehavior p) (hw : IsPairLaw w)
    (h10 : p true false false false = 0) (h01 : p false true false false = 0)
    (hs : 0 < siftingProbability p w) :
    (∀ A B, A ≠ B → acceptedMass p w A B = 0) ∧
    (∑ A, ∑ B, if A = B then acceptedLaw p w A B else 0) = 1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P47
