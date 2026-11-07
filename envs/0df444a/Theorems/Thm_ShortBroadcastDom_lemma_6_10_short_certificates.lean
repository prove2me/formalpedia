-- Prove2me | Theorems.Thm_ShortBroadcastDom_lemma_6_10_short_certificates
-- name    : ShortBroadcastDom.lemma_6_10_short_certificates
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:27:12.79166+00:00
-- url     : https://prove2.me/theorems/3708531c-2ab8-445c-92e0-01060e94a869
-- title:
--   Lemma 6.10 — integer $q$-fold covers of cost at most $(q+2\lceil a\rceil)\tau_{R,c}(H)$
-- statement:
--   Let $a\ge 1$ and let $H$ be a finite graph all of whose subgraphs have density at most $a$; put $p=\lceil a\rceil$. Let $R\subseteq V(H)$ be a demand set and $c_v>0$ positive real vertex costs, and write $\tau=\tau_{R,c}(H)$. Then for every positive integer $q$ there are nonnegative integers $\mu_v$ (the number of copies of each candidate) with
--
--   $$
--   \sum_{v\in N_H[r]}\mu_v\ge q\quad(r\in R),\qquad \sum_v c_v\mu_v\le(q+2p)\,\tau.
--   $$
--
--   Dividing by $q$ gives a fractional cover with common denominator $q$ and cost at most $(1+2p/q)\tau$: a short description of a near-optimal fractional solution, which the local solver of Lemma 6.12 searches for.
--
--   Differences from the source:
--   - encoding: p = ⌈a⌉ → ⌈a⌉₊ (natural-number ceiling); reason: equal for a ≥ 1
--   - encoding: τ = min of the LP → sInf of the feasible objective values; reason: the feasible set is nonempty and bounded below by 0 for positive costs, so this is the minimum
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §6.4.1, p.34 (PDF p.37), Lemma 6.10

import Mathlib
import Definitions.Def_ShortBroadcastDom_SubgraphDensityLE
import Definitions.Def_ShortBroadcastDom_tauOn

namespace ShortBroadcastDom

/-- **Lemma 6.10 (short integer certificates).** Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §6.4.1, p.34 (PDF 37): "Assume a ≥ 1 and
that every subgraph of H has a ratio of edges to vertices of at most a. Put p = ⌈a⌉ and consider a
demand set R ⊆ V(H) with positive vertex costs cv. Write τ = τR,c(H). For every positive integer q,
there are nonnegative integers µv giving the number of copies of each candidate, such that
∑_{v∈NH[r]} µv ≥ q (r ∈ R), ∑_v cvµv ≤ (q + 2p)τ."

**Formalization Note** Costs are positive reals (p.15: "the same notation is used with positive
real costs"); `p = ⌈a⌉₊`, which equals `⌈a⌉` for `a ≥ 1`. -/
theorem lemma_6_10_short_certificates {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (a : ℝ) (ha : 1 ≤ a) (hH : SubgraphDensityLE a H) (R : Finset V) (c : V → ℝ)
    (hc : ∀ v, 0 < c v) (q : ℕ) (hq : 0 < q) :
    ∃ μ : V → ℕ, (∀ r ∈ R, q ≤ ∑ v ∈ closedNbhd H r, μ v) ∧
      ∑ v, c v * (μ v : ℝ) ≤ ((q : ℝ) + 2 * (⌈a⌉₊ : ℝ)) * tau H R c := by sorry

end ShortBroadcastDom
