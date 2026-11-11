-- Prove2me | Theorems.Thm_TightContinualCounting_LowerBounds_lemma_3
-- name    : TightContinualCounting.LowerBounds.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:16.162573+00:00
-- url     : https://prove2.me/theorems/38174711-97d3-47e7-9913-0c42f152e793
-- title:
--   Lemma 3 — approximate group privacy including zero epsilon
-- statement:
--   Let $M$ be an $(\varepsilon,\delta)$-DP mechanism on $\{0,1\}^n$ with probability laws on any measurable output space $\mathcal Y$, where $\varepsilon,\delta\ge0$. Let $x,x'$ differ in at most $k\ge0$ coordinates, and let $S\subseteq\mathcal Y$ be measurable. With $\delta_k=\delta\sum_{i=0}^{k-1}e^{i\varepsilon}$,
--
--   $$
--   M(x)(S)\le e^{k\varepsilon}M(x')(S)+\delta_k.
--   $$
--
--   The geometric sum also covers $\varepsilon=0$, giving $\delta_k=\delta k$, and $k=0$, giving $\delta_0=0$. This is the privacy comparison between the two repeated-bit inputs in Lemma 12.
--
--   Differences from the source:
--   - encoding: coordinates [d]={1,…,d} → coordinates Fin d={0,…,d−1}; reason: the order-preserving reindexing preserves every interval, vector and finite sum
--   - encoding: randomized mechanisms and probabilities of measurable events → families of probability measures and event masses in ℝ≥0∞; reason: this is the same model, including arbitrary continuous output laws and infinite loss
--   - encoding: δ_k as a geometric sum with an optional quotient formula → the finite geometric sum only; reason: it computes exactly the stated slack and retains ε=0 without a zero denominator
-- source:
--   Charlie Harrison, Ethan Leeman, Tight Lower Bounds for Differentially Private Continual Counting, STOC 2027 submission #1453 (October 2026), Lemma 3 p.5; Definition 2 p.4

import Mathlib
import Definitions.Def_ContinualCounting_IsApproxDP
import Definitions.Def_TightContinualCounting_LowerBounds_parameters

open MeasureTheory
open scoped ENNReal

namespace TightContinualCounting.LowerBounds

/-- Lemma 3 (Group privacy), p.5; measurable events as in Definition 2. -/
theorem lemma_3 {n : ℕ} {Y : Type*} [MeasurableSpace Y]
    (M : (Fin n → Bool) → Measure Y) (hM : ∀ x, IsProbabilityMeasure (M x))
    (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hDP : ContinualCounting.IsApproxDP (fun x x' => hamming x x' ≤ 1) M ε δ)
    (k : ℕ) (x x' : Fin n → Bool) (hk : hamming x x' ≤ k)
    (S : Set Y) (hS : MeasurableSet S) :
    M x S ≤ ENNReal.ofReal (Real.exp ((k : ℝ) * ε)) * M x' S +
      ENNReal.ofReal (groupDelta ε δ k) := by sorry

end TightContinualCounting.LowerBounds
