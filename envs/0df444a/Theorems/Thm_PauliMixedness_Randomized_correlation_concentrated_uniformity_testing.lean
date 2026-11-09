-- Prove2me | Theorems.Thm_PauliMixedness_Randomized_correlation_concentrated_uniformity_testing
-- name    : PauliMixedness.Randomized.correlation_concentrated_uniformity_testing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:54:44.610581+00:00
-- url     : https://prove2.me/theorems/f3afe425-15f9-4ff7-8916-3b24e63b8c6e
-- title:
--   Theorem 2.4 — correlation-concentrated uniformity testing
-- statement:
--   There is one absolute $C>0$ such that for every $1\le k\le N$, $0<\Delta,\beta\le1$ and $0<\delta\le1$, the amplified Algorithm 2 defined here uses
--
--   $$n\le C\frac{\sqrt{\binom Nk}}{\beta\Delta}\ln\frac1\delta$$
--
--   samples. It declares NO on the uniform cube distribution with probability at least $1-\delta$. For every distribution $p$ with $E_k(p)\ge\beta E(p)$ and $E_k(p)\ge\beta\Delta$, it declares YES with probability at least $1-\delta$. Both clauses include all sample and decision randomness; there is no full-support assumption.
--
--   This is the classical testing guarantee used for product Pauli measurement outcomes. The single base statistic retains constants 400 and 50, and two independent arrays. The confidence guarantee refers to the independent majority amplification in the proof.
--
--   Differences from the source:
--   - encoding: sign strings in $\{-1,1\}^N$ and one-based wires → $\mathbb F_2^N$ with sign $(-1)^b$ and zero-based finite wires; reason: bijective reindexing preserves every outcome, character and state
--   - encoding: a nonintegral displayed base sample count and black-box amplification → ceiling-rounded arrays, $2\lceil8\ln(1/\delta)\rceil+1$ fresh repetitions for $\delta<1/2$, and a zero-sample fair decision otherwise; reason: integer rounding and an explicit majority realize the stated sample order and confidence, including δ=1
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #231 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/231.pdf, Theorem 2.4 p.7; Algorithm 2 p.16; proof pp.24–26

import Definitions.Def_PauliMixedness_Randomized_KrawtCheck

namespace PauliMixedness.Randomized

/-- Theorem 2.4 p.7, Algorithm 2 p.16 and its amplification p.26. -/
theorem correlation_concentrated_uniformity_testing :
    ∃ C : ℝ, 0 < C ∧ ∀ N k : ℕ, 1 ≤ k → k ≤ N →
      ∀ Δ β δ : ℝ, 0 < Δ → Δ ≤ 1 → 0 < β → β ≤ 1 → 0 < δ → δ ≤ 1 →
        (krawtSamples N k Δ β δ : ℝ) ≤
          C * Real.sqrt (N.choose k : ℝ) / (β * Δ) * Real.log (1 / δ) ∧
        1 - δ ≤ 1 - krawtYesProbability (cubeUniform N) k Δ β δ ∧
        ∀ p : PMF (Cube N), WiseCorrelated p Δ k β →
          1 - δ ≤ krawtYesProbability p k Δ β δ := by sorry

end PauliMixedness.Randomized
