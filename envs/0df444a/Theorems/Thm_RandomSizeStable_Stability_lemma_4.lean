-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_lemma_4
-- name    : RandomSizeStable.Stability.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:44.916551+00:00
-- url     : https://prove2.me/theorems/64e7cb6a-894f-4217-827a-f719d679d953
-- title:
--   Lemma 4 — measurable-set rearrangement (4.3)
-- statement:
--   Let $D$ be any positive-integer draw law with generating function $\phi_D$, primitive $\Phi_D$ and benchmark $\mu_D$. Suppose $0\le a\le p\le A\le1$, and $S\subseteq[0,A]$ is any Lebesgue-measurable set of length $p$ containing $[0,a]$ up to endpoints. Then
--   $$\int_S(\phi_D(u)-\mu_D)\,du\le
--   \Phi_D(a)+\Phi_D(A)-\Phi_D(a+A-p)-p\mu_D.$$
--   The domain includes all endpoint cases and arbitrary measurable sets, without restricting to unions of ranking blocks.
--
--   This gives the scalar upper bound for a marked region of known length and cutoffs.
--
--   Differences from the source:
--   - encoding: a positive-integer-valued random variable D → a PMF on the positive integers; reason: only the law enters these claims; countably infinite support and infinite mean remain allowed
--   - encoding: a measurable set of length p containing [0,a] up to endpoints → NullMeasurableSet for Lebesgue volume, volume S = ofReal p, and (0,a) ⊆ S; reason: null measurability represents the completed Lebesgue sigma algebra; only the two endpoints may be omitted
-- source:
--   Nisarg Shah, Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission #1342 (October 2026), p. 13, Lemma 4, Equation (4.3).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankBlocks

set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion

namespace RandomSizeStable.Stability

/-- Lemma 4, p.13: all Lebesgue-measurable sets, not merely rank blocks.
NullMeasurableSet with respect to volume is measurability in its completion. -/
theorem lemma_4 (D : PMF ℕ+) (a p A : ℝ)
    (ha : 0 ≤ a) (hap : a ≤ p) (hpA : p ≤ A) (hA : A ≤ 1)
    (S : Set ℝ) (hS : NullMeasurableSet S volume) (hsub : S ⊆ Set.Icc 0 A)
    (hlen : volume S = ENNReal.ofReal p) (hcontains : Set.Ioo 0 a ⊆ S) :
    (∫ u in S, (pgf D u - benchmark D)) ≤
      primitive D a + primitive D A - primitive D (a + A - p) - p * benchmark D := by sorry

end RandomSizeStable.Stability
