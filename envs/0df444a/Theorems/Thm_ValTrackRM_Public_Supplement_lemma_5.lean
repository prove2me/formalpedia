-- Prove2me | Theorems.Thm_ValTrackRM_Public_Supplement_lemma_5
-- name    : ValTrackRM.Public.Supplement.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T04:02:37.607672+00:00
-- url     : https://prove2.me/theorems/42da8c2f-88fa-41a1-80fd-750f6b12fa79
-- title:
--   Lemma 5 — first-failure partitions and matching masses
-- statement:
--   For either Samp or the hypothetical augmented Exp, let $H_t$ record failure flags, prices and valuations through time $t-1$, and the failure flag at time $t$. Put $F_{T+1}=1$ and let $\mathcal F_t$ contain every history with first failure at $t$. For each policy the events form a disjoint exhaustive partition:
--   $$\bigcup_{t=1}^{T+1}\ \bigcup_{h\in\mathcal F_t}\{H_t=h\}.$$
--   Furthermore, for every $1\le t\le T+1$ and every such history,
--   $$\Pr[H_t^{\mathrm{Samp}}=h]=\Pr[H_t^{\mathrm{Exp}}=h].$$
--   The partition is stated path by path as unique membership, separately for both algorithms. No positive-mass restriction removes impossible histories. These are the three clauses needed for comparing revenue by first failure.
--
--   Differences from the source:
--
--   - generalization: Algorithm 1 leaves arg-min ties unspecified → every fixed minimum-level selector is allowed; reason: the assignment must be deterministic for a fixed valuation prefix; no special tie-break is used
--   - encoding: independent valuations are described as probability vectors → Mathlib PMF inputs and their explicit product masses; reason: every finite grid distribution is included and independence is constructed, not assumed from a conclusion
--   - encoding: prices r^(1),...,r^(m),infinity and valuation values → price codes 0,...,m, with m meaning rejection, and valuation indices 0,...,m; reason: this is a bijection on the strictly increasing positive price grid; rejection has zero revenue
--   - generalization: competitive horizons T are positive → the revenue and law statements also include T=0; reason: the empty execution and empty optimum both have revenue zero
--   - generalization: Lemma 5 partitions the sample paths of the two algorithms → unique first-failure membership holds for every enumerated execution leaf, including leaves of weight zero; reason: matchesFirst uses the first true flag, or the deterministic terminal flag; zero-weight leaves also have exactly T observations and therefore satisfy the same partition
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, p. 22, Lemma 5

import Mathlib
import Definitions.Def_ValTrackRM_Public_Supplement_Sampling

namespace ValTrackRM.Public.Supplement

theorem lemma_5
    (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ)
    (hr0 : r 0 = 0) (hr : ∀ j < m, r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : isMin sel)
    (ν : ℕ → PMF (Fin (m + 1))) (C : ℕ) (hC : 1 ≤ C) (T : ℕ) :
    firstPartition (publicRun r sel ν C false T) T ∧
    firstPartition (publicRun r sel ν C true T) T ∧
    (∀ (t : ℕ), 1 ≤ t → t ≤ T + 1 → ∀ h : FirstHistory m t,
      firstMass r sel ν C T false t h = firstMass r sel ν C T true t h) := by sorry

end ValTrackRM.Public.Supplement
