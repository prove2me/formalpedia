-- Prove2me | Theorems.Thm_ValTrackRM_Public_Supplement_lemma_7
-- name    : ValTrackRM.Public.Supplement.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:04:37.143149+00:00
-- url     : https://prove2.me/theorems/e4c6d23f-69d5-4e75-a82a-bd9cbd3277b0
-- title:
--   Lemma 7 — inverse-square first-failure bound
-- statement:
--   For positive inventory $k$, a nonempty strictly increasing positive grid, independent valuation laws, and any positive integer sampling constant $C$, let $\mathcal F_t$ be the first-failure histories of Samp at time $t$. For every $1\le t\le T$,
--   $$\sum_{h\in\mathcal F_t}\Pr[H_t^{\mathrm{Samp}}=h]\le\frac{1}{eCt^2}.$$
--   The left side is computed from the actual bounded sampling execution law. This is an unconditional first-failure probability estimate; it is neither a pathwise loss claim nor a high-probability approximation.
--
--   Differences from the source:
--
--   - generalization: Algorithm 1 leaves arg-min ties unspecified → every fixed minimum-level selector is allowed; reason: the assignment must be deterministic for a fixed valuation prefix; no special tie-break is used
--   - encoding: independent valuations are described as probability vectors → Mathlib PMF inputs and their explicit product masses; reason: every finite grid distribution is included and independence is constructed, not assumed from a conclusion
--   - encoding: prices r^(1),...,r^(m),infinity and valuation values → price codes 0,...,m, with m meaning rejection, and valuation indices 0,...,m; reason: this is a bijection on the strictly increasing positive price grid; rejection has zero revenue
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, p. 23, Lemma 7

import Mathlib
import Definitions.Def_ValTrackRM_Public_Supplement_Sampling

namespace ValTrackRM.Public.Supplement

theorem lemma_7
    (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ)
    (hr0 : r 0 = 0) (hr : ∀ j < m, r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : isMin sel)
    (ν : ℕ → PMF (Fin (m + 1))) (C : ℕ) (hC : 1 ≤ C) (T t : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ T) :
    firstFailureMass r sel ν C T t ≤ 1 / (Real.exp 1 * (C : ℝ) * (t : ℝ) ^ 2) := by sorry

end ValTrackRM.Public.Supplement
