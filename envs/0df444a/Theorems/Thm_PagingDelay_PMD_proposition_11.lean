-- Prove2me | Theorems.Thm_PagingDelay_PMD_proposition_11
-- name    : PagingDelay.PMD.proposition_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:05.103217+00:00
-- url     : https://prove2.me/theorems/e29f29ed-808e-4a65-ac2f-80e959418b35
-- title:
--   Proposition 11 — fractional delay cost
-- statement:
--   For every valid PMD instance, with each request's delay weighted by its missing mass $\alpha_r$ immediately before arrival,
--
--   $$C_{\rm delay}\le C_{\rm fetch}+5\sum_{\nu\in S_{\rm crit}}|\lambda^{(\nu)}|.$$
--
--   The factor is exactly five. Infinite delay remains representable until Lemma 2 establishes that every request is served.
--
--   Differences from the source:
--   - encoding: pages indexed by 1 through n → pages indexed by Fin n; reason: a bijective reindexing of the same finite page universe
--   - reading: any tie-breaking rule suffices → all page orders π and all designated initial pages i₀ outside O₀; reason: an arbitrary order resolves simultaneous critical times and equal effective deadlines; no order is fixed
--   - encoding: Algorithm 1 with instantaneous services and eventual service → explicit transition recursion with |σ|+1 next-event iterations, transient states, optional infima and zero-denominator guards; reason: each critical service serves a pending request, so there are at most |σ|; the guards only totalize undefined inputs, and Lemma 2 states full service rather than assuming it
--   - encoding: the first nonnegative hitting time |λ| and natural logarithm L → guarded real infimum and L = log(2k+1); reason: on the stated valid domain the hitting set is nonempty, bounded below and closed; k≥1 makes L positive
--   - encoding: nonnegative fractional delay cost → ENNReal delay, with the finite real right side embedded by ofReal; reason: unserved requests do not acquire a zero default value
-- source:
--   Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Proposition 11 — fractional delay cost, p. 14. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/453.pdf

import Definitions.Def_PagingDelay_PMD_Algorithm

namespace PagingDelay.PMD
open scoped BigOperators

/-- Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Proposition 11 — fractional delay cost, p. 14. -/
theorem proposition_11 (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (w : Fin n → ℝ) (hw : PMDWeights w)
    (O₀ : Finset (Fin n)) (hO₀ : O₀.card = k)
    (i₀ : Fin n) (hi₀ : i₀ ∉ O₀) (π : Fin n ≃ Fin n)
    (σ : Instance n) (hσ : ValidInstance σ) :
    fractionalDelay k (run k w O₀ i₀ π σ) σ ≤
      ENNReal.ofReal (fractionalFetch w (run k w O₀ i₀ π σ) + 5 * criticalLength k w (run k w O₀ i₀ π σ)) := by sorry

end PagingDelay.PMD
