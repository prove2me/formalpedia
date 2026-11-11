-- Prove2me | Theorems.Thm_SubexpPermanent_Main_fact_4_5
-- name    : SubexpPermanent.Main.fact_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:01:23.258241+00:00
-- url     : https://prove2.me/theorems/59db040c-9eda-4e99-ad26-e985933e6d4d
-- title:
--   Fact 4.5 — in a bipartite graph, unmatched indicators are nonnegatively correlated across parts and nonpositively within a part; $\mu_{uv}=w_{uv}\Pr(u,v\text{ unmatched})\ge w_{uv}q(u)q(v)$
-- statement:
--   Let $G$ be a finite simple bipartite graph with positive edge weights $w$, let $M\sim\nu_{G,w}$, and let $Y_u$ be $1$ if $u$ is unmatched in $M$ and $0$ otherwise. For distinct vertices $u,v$,
--   $$\mathrm{Cov}(Y_u,Y_v)\ge0\ \text{ if $u,v$ lie in opposite parts},\qquad \mathrm{Cov}(Y_u,Y_v)\le0\ \text{ if they lie in the same part}.$$
--   In particular, for every edge $uv$,
--   $$\mu_{w,uv}=w_{uv}\Pr_w(u,v\text{ both unmatched in }M)\ge w_{uv}\,q_G(u)\,q_G(v).$$
--   These are the Heilmann–Lieb correlation inequalities. The last one is the positive-correlation step in the proof of the bound (21) on unmatched rows (Lemma 6.3).
--
--   Differences from the source:
--
--   - encoding: the parts of the bipartite graph G → the two colour classes of a proper 2-colouring c : V → Bool, for every such c; reason: a bipartite graph is one with a proper 2-colouring; when G is disconnected the parts are not unique and the statement holds for each choice
--   - encoding: Cov(Y_u, Y_v) → Pr(u, v both unmatched) − q_G(u) q_G(v) (unmatchedCov); reason: E[Y_u Y_v] = Pr(both unmatched) for indicators
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), pp. 13–14, Fact 4.5

import Mathlib
import Definitions.Def_SubexpPermanent_Main_Matchings

namespace SubexpPermanent.Main

/-- Fact 4.5 (correlations of unmatched vertices in bipartite graphs), pp. 13–14. The parts of
the bipartite graph are the two colour classes of a proper 2-colouring `c`. -/
theorem fact_4_5 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (w : Sym2 V → ℝ) (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    (c : V → Bool) (hc : ∀ u v : V, G.Adj u v → c u ≠ c v) :
    (∀ u v : V, u ≠ v → c u ≠ c v → 0 ≤ unmatchedCov G w Finset.univ u v) ∧
    (∀ u v : V, u ≠ v → c u = c v → unmatchedCov G w Finset.univ u v ≤ 0) ∧
    ∀ u v : V, G.Adj u v →
      edgeProb G w Finset.univ s(u, v) = w s(u, v) * bothUnmatchedProb G w Finset.univ u v ∧
      w s(u, v) * unmatchedProb G w Finset.univ u * unmatchedProb G w Finset.univ v ≤
        w s(u, v) * bothUnmatchedProb G w Finset.univ u v := by sorry

end SubexpPermanent.Main
