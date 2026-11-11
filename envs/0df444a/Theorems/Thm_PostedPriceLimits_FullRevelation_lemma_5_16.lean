-- Prove2me | Theorems.Thm_PostedPriceLimits_FullRevelation_lemma_5_16
-- name    : PostedPriceLimits.FullRevelation.lemma_5_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:32.273813+00:00
-- url     : https://prove2.me/theorems/0e815b34-131d-45a7-abec-9ee07b334fe8
-- title:
--   Lemma 5.16 — expected owner welfare is at most $(5+2/n)\kappa|Z_1|$
-- statement:
--   In the construction of §5, for all sufficiently large $n$ and every (measurable) deterministic mechanism of the analysis model, if $S_1,\dots,S_n$ is the allocation produced by the mechanism then
--   $$\mathbb E\Big[\sum_{i\in[n]}w_{\pi(i)}(S_i\cap Z_{\pi(i)})\Big]\le\Big(5+\frac2n\Big)\kappa|Z_1|.$$
--   The expectation is unconditional: the exceptional event $\mathcal E^c$ is paid for inside the bound.
--
--   Together with Lemma 5.15 this bounds the expected welfare of every mechanism by $(5+3/n)\kappa|Z_1|$, while the expected optimum is at least $n\kappa|Z_1|$.
--
--   Differences from the source:
--   - encoding: π, τ_t, N_{t,i}, ψ_{t,γ}, ξ_{t,γ} and the owner-rank draws sampled as described on printed pp.15–17 → the same objects as deterministic functions of independent Unif[0,1] labels (inversion for ψ, ξ = 2U, coin U < 1/m, rank by cumulative intervals) together with uniform injections τ_t and a uniform permutation π; reason: a coupling with exactly the source's joint law of all objects the statements mention; the mechanism never sees the raw labels
--   - encoding: E[∑_i w_{π(i)}(S_i ∩ Z_{π(i)})] → lower Lebesgue integral ∫⁻ of ENNReal.ofReal of the (nonnegative) integrand, bounded by ENNReal.ofReal of the right-hand side; reason: the integrand is nonnegative and bounded, so this is the expectation; no junk value can make the bound vacuous
--   - encoding: an arbitrary deterministic mechanism (expectations/probabilities over the instance taken implicitly) → a deterministic analysis mechanism whose proposed prices are measurable functions of the randomness (PricesMeasurable); reason: routine measurability that only makes the probability/expectation defined; mechanisms obtained from OFR mechanisms (whose inputs take finitely many values) satisfy it
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Lemma 5.16, p.25 (PDF 26); PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Construction
import Definitions.Def_PostedPriceLimits_FullRevelation_Analysis
open MeasureTheory

namespace PostedPriceLimits.FullRevelation

/-- Lemma 5.16 (for all sufficiently large `n`). For every deterministic mechanism of the
analysis model with allocation `S_1, …, S_n`,
`E[∑_{i ∈ [n]} w_{π(i)}(S_i ∩ Z_{π(i)})] ≤ (5 + 2/n) κ|Z_1|`. -/
theorem lemma_5_16 : ∃ N : ℕ, ∀ n ≥ N, ∀ M : AnalysisMech n, M.PricesMeasurable →
    ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
        ownerVal ω (perm ω i) (localPart n (M.allocation ω i) (perm ω i))) ∂(latentLaw n) ≤
      ENNReal.ofReal ((5 + 2 / (n : ℝ)) * kappa n * blockSize n) := by sorry

end PostedPriceLimits.FullRevelation
