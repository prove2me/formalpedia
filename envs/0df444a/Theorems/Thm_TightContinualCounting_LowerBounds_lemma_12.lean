-- Prove2me | Theorems.Thm_TightContinualCounting_LowerBounds_lemma_12
-- name    : TightContinualCounting.LowerBounds.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:10.02677+00:00
-- url     : https://prove2.me/theorems/3754b54f-d0b2-455c-b963-644744de66f0
-- title:
--   Lemma 12 — privacy upper bound for either probe score
-- statement:
--   Let $n,H,k\ge1$ with $k4^H\le n$, and let $M$ be an $(\varepsilon,\delta)$-DP probability-law mechanism on length-$n$ binary streams, where $\varepsilon,\delta\ge0$. Sample $X\in\{0,1\}^{4^H}$ and $J\in[4^H]$ independently uniformly, draw $W\sim M(E_k(X))$ independently of $J$ conditional on $X$, and define $Y=(W-A_nE_k(X\oplus e_J))_{[k4^H]}/k$. For $a>1$ and either $\phi\in\{\mathrm{mean},\mathrm{mid}\}$,
--
--   $$
--   \Pr_{X,J,M}[S_\phi(J,Y)\ge H/4]\le2\exp\left(k\varepsilon-\frac{H}{32a^2}\right)+\delta_k,
--   \qquad\delta_k=\delta\sum_{i=0}^{k-1}e^{i\varepsilon}.
--   $$
--
--   The statement compares score success to the privacy budget without any output support or moment assumption. Combined with the pointwise accuracy lower bound, it constrains both loss measures in Theorem 1.
--
--   Differences from the source:
--   - encoding: coordinates [d]={1,…,d} → coordinates Fin d={0,…,d−1}; reason: the order-preserving reindexing preserves every interval, vector and finite sum
--   - encoding: randomized mechanisms and probabilities of measurable events → families of probability measures and event masses in ℝ≥0∞; reason: this is the same model, including arbitrary continuous output laws and infinite loss
--   - encoding: probability over X,J,M → a normalized finite sum of output-law event masses; reason: only X and J are finite, while the output measure itself remains unrestricted
--   - encoding: distance at most one in Definition 2 → the published IsDP predicate for distance exactly one; reason: for nonnegative ε,δ the omitted diagonal event inequality is automatic, so the predicates are equivalent
-- source:
--   Charlie Harrison, Ethan Leeman, Tight Lower Bounds for Differentially Private Continual Counting, STOC 2027 submission #1453 (October 2026), Lemma 12 p.13, proof pp.13–14

import Mathlib
import Definitions.Def_ContinualCounting_IsDP
import Definitions.Def_TightContinualCounting_LowerBounds_parameters
import Definitions.Def_TightContinualCounting_LowerBounds_sampling

open MeasureTheory
open scoped ENNReal

namespace TightContinualCounting.LowerBounds

/-- Lemma 12 (Privacy upper bound), p.13. -/
theorem lemma_12 (n H k : ℕ) (hn : 1 ≤ n) (hH : 1 ≤ H) (hk : 1 ≤ k)
    (hq : k * 4 ^ H ≤ n)
    (M : (Fin n → Bool) → Measure (Fin n → ℝ)) (hM : ∀ x, IsProbabilityMeasure (M x))
    (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hDP : ContinualCounting.IsDP M ε δ)
    (a : ℝ) (ha : 1 < a) (φ : ProbeRule) :
    taggingProbability H k hq M a φ ≤
      ENNReal.ofReal (2 * Real.exp ((k : ℝ) * ε - (H : ℝ) / (32 * a ^ 2)) +
        groupDelta ε δ k) := by sorry

end TightContinualCounting.LowerBounds
