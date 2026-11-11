-- Prove2me | Theorems.Thm_TightContinualCounting_LowerBounds_lemma_6
-- name    : TightContinualCounting.LowerBounds.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:00.251753+00:00
-- url     : https://prove2.me/theorems/0d1592bc-68d4-4295-a6a2-4a2958f437e1
-- title:
--   Lemma 6 — independence of the flip index and randomized output
-- statement:
--   Let $n\ge1$ and let $F(x)$ be any probability law on an arbitrary measurable space $\mathcal Y$ for each $x\in\{0,1\}^n$. Sample $X$ uniformly on $\{0,1\}^n$ and $J$ independently uniformly on $[n]$, then randomize according to $F(X\oplus e_J)$ independently of $J$ conditional on the flipped input. With $\bar F=2^{-n}\sum_x F(x)$, the joint law satisfies
--
--   $$
--   \mathcal L(J,F(X\oplus e_J))=\operatorname{Unif}([n])\otimes\bar F.
--   $$
--
--   In particular the selected index and randomized output are independent. This formulation includes the arbitrary randomized functions in the source and is used for the residual on a fresh run of the mechanism at the flipped input.
--
--   Differences from the source:
--   - encoding: coordinates [d]={1,…,d} → coordinates Fin d={0,…,d−1}; reason: the order-preserving reindexing preserves every interval, vector and finite sum
--   - encoding: independent internal randomness of randomized f and independence of J,f(X xor e_J) → probability-law family F and exact product factorization of the finite-mixture joint law; reason: finite input laws describe arbitrary randomization, and the second marginal is the computed uniform mixture, so this is the same independence assertion
-- source:
--   Charlie Harrison, Ethan Leeman, Tight Lower Bounds for Differentially Private Continual Counting, STOC 2027 submission #1453 (October 2026), Lemma 6 p.6

import Mathlib
import Definitions.Def_TightContinualCounting_LowerBounds_sampling

open MeasureTheory

namespace TightContinualCounting.LowerBounds

/-- Lemma 6, p.6: equality of joint laws expresses independence for arbitrary randomized output. -/
theorem lemma_6 {n : ℕ} (hn : 1 ≤ n) {Y : Type*} [MeasurableSpace Y]
    (F : (Fin n → Bool) → Measure Y) (hF : ∀ x, IsProbabilityMeasure (F x)) :
    flippedJointLaw F = (uniformFinite (Fin n)).prod (averagedLaw F) := by sorry

end TightContinualCounting.LowerBounds
