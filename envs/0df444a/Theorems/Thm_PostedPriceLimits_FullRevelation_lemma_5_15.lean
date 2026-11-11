-- Prove2me | Theorems.Thm_PostedPriceLimits_FullRevelation_lemma_5_15
-- name    : PostedPriceLimits.FullRevelation.lemma_5_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:11.743967+00:00
-- url     : https://prove2.me/theorems/0627f80a-341e-4bd4-959d-3c8d0a16a013
-- title:
--   Lemma 5.15 — expected non-owner welfare is at most $\kappa|Z_1|/n$
-- statement:
--   In the construction of §5, for all sufficiently large $n$,
--   $$\mathbb E\Big[\sum_{t,i\in[n]}v_{t,i}(Z_t)\Big]\le\frac{\kappa|Z_1|}{n},$$
--   where the sum runs over all $n^2$ block-bidder pairs, including the non-owner valuation $v_{t,i}$ of the owner of $Z_t$. The expectation is unconditional (no good event).
--
--   Since valuations are monotone, this bounds the non-owner part of any mechanism's welfare.
--
--   Differences from the source:
--   - encoding: π, τ_t, N_{t,i}, ψ_{t,γ}, ξ_{t,γ} and the owner-rank draws sampled as described on printed pp.15–17 → the same objects as deterministic functions of independent Unif[0,1] labels (inversion for ψ, ξ = 2U, coin U < 1/m, rank by cumulative intervals) together with uniform injections τ_t and a uniform permutation π; reason: a coupling with exactly the source's joint law of all objects the statements mention; the mechanism never sees the raw labels
--   - encoding: E[∑_{t,i} v_{t,i}(Z_t)] → lower Lebesgue integral ∫⁻ of ENNReal.ofReal of the (nonnegative) integrand, bounded by ENNReal.ofReal of the right-hand side; reason: the integrand is nonnegative and bounded, so this is the expectation; no junk value can make the bound vacuous
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Lemma 5.15, p.24 (PDF 25); PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Construction
open MeasureTheory

namespace PostedPriceLimits.FullRevelation

/-- Lemma 5.15 (for all sufficiently large `n`).
`E[∑_{t,i ∈ [n]} v_{t,i}(Z_t)] ≤ κ|Z_1|/n`. -/
theorem lemma_5_15 : ∃ N : ℕ, ∀ n ≥ N,
    ∫⁻ ω, ENNReal.ofReal (∑ t : Fin n, ∑ i : Fin n, nonOwnerVal ω t i Finset.univ) ∂(latentLaw n) ≤
      ENNReal.ofReal ((kappa n : ℝ) * blockSize n / n) := by sorry

end PostedPriceLimits.FullRevelation
