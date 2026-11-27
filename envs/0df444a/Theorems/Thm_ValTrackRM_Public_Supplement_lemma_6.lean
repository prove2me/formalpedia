-- Prove2me | Theorems.Thm_ValTrackRM_Public_Supplement_lemma_6
-- name    : ValTrackRM.Public.Supplement.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T04:03:36.554789+00:00
-- url     : https://prove2.me/theorems/b3a29dba-112d-48b1-a2f1-42277b14ba82
-- title:
--   Lemma 6 — conditional revenue-loss bound
-- statement:
--   Let the valuations be independent with arbitrary grid laws, let $C\ge1$ be the sampling constant, and let $h\in\mathcal F_t$ be any first-failure history at a time $1\le t\le T$. For Samp and the hypothetical augmented Exp,
--   $$
--   \mathbb E[\mathrm{ALG}^{\mathrm{Exp}}\mid H_t^{\mathrm{Exp}}=h]-\mathbb E[\mathrm{ALG}^{\mathrm{Samp}}\mid H_t^{\mathrm{Samp}}=h]\le\mathbb E[\mathrm{OPT}(V_1,\ldots,V_T)].
--   $$
--   The right side is the unconditional expected optimum of the full independent valuation sequence. This bounds the expected loss associated with a first sampling failure, including histories whose current inventory is zero.
--
--   **Formalization Note** All histories remain quantified. Finite conditional weighted expectations are assigned zero at a zero-mass conditioning history; on positive-mass histories they have the usual meaning.
--
--   Differences from the source:
--
--   - generalization: Algorithm 1 leaves arg-min ties unspecified → every fixed minimum-level selector is allowed; reason: the assignment must be deterministic for a fixed valuation prefix; no special tie-break is used
--   - encoding: independent valuations are described as probability vectors → Mathlib PMF inputs and their explicit product masses; reason: every finite grid distribution is included and independence is constructed, not assumed from a conclusion
--   - encoding: conditional expectations are used on first-failure histories → finite conditional weighted sums divide by event mass and equal zero at a zero-mass history; reason: this keeps every history in the source quantifier and agrees with ordinary conditioning whenever its probability is positive
--   - encoding: prices r^(1),...,r^(m),infinity and valuation values → price codes 0,...,m, with m meaning rejection, and valuation indices 0,...,m; reason: this is a bijection on the strictly increasing positive price grid; rejection has zero revenue
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, p. 23, Lemma 6

import Mathlib
import Definitions.Def_ValTrackRM_Public_Supplement_Sampling

namespace ValTrackRM.Public.Supplement

theorem lemma_6
    (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ)
    (hr0 : r 0 = 0) (hr : ∀ j < m, r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : isMin sel)
    (ν : ℕ → PMF (Fin (m + 1))) (C : ℕ) (hC : 1 ≤ C) (T t : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ T) (h : FirstHistory m t) :
    conditionalRevenue r sel ν C T true t h - conditionalRevenue r sel ν C T false t h ≤
      expectedOpt r k ν T := by sorry

end ValTrackRM.Public.Supplement
