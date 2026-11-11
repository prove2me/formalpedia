-- Prove2me | Theorems.Thm_SubexpPermanent_Main_lemma_4_6
-- name    : SubexpPermanent.Main.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:01:21.839397+00:00
-- url     : https://prove2.me/theorems/86ea532e-203d-4a94-91fd-8825879dae51
-- title:
--   Lemma 4.6 — deleting $u$ moves the other unmatched probabilities by at most $1-q_G(u)$ in total (equality if bipartite); deleting $S$ by at most $|S|$
-- statement:
--   Let $G=(V,E)$ be a finite simple graph with positive edge weights, and $q_H(v)$ the probability that $v$ is unmatched in the matching distribution of $H$. For every $u\in V$,
--   $$\sum_{v\in V\setminus\{u\}}\big|q_{G-u}(v)-q_G(v)\big|\le 1-q_G(u)\qquad(14),$$
--   with equality when $G$ is bipartite. For every $S\subseteq V$,
--   $$\sum_{v\in V\setminus S}\big|q_{G-S}(v)-q_G(v)\big|\le|S|\qquad(15).$$
--   Inequality (14) controls the error the counting algorithm of Theorem 7.1 makes when it uses estimates computed for the original graph in place of the graph after deletions.
--
--   Differences from the source:
--
--   - encoding: G − u, G − S → the subgraphs induced on Finset.univ.erase u and Finset.univ \ S; reason: the same weighted graphs
--   - encoding: G bipartite → G.Colorable 2; reason: a graph is bipartite iff it has a proper 2-colouring
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 14, Lemma 4.6, eqs. (14)–(15)

import Mathlib
import Definitions.Def_SubexpPermanent_Main_Matchings

namespace SubexpPermanent.Main

/-- Lemma 4.6 (effect of deleting vertices), p. 14. -/
theorem lemma_4_6 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (w : Sym2 V → ℝ) (hw : ∀ e ∈ G.edgeSet, 0 < w e) :
    (∀ u : V,
      ∑ v ∈ Finset.univ.erase u,
          |unmatchedProb G w (Finset.univ.erase u) v - unmatchedProb G w Finset.univ v| ≤
        1 - unmatchedProb G w Finset.univ u) ∧
    (G.Colorable 2 → ∀ u : V,
      ∑ v ∈ Finset.univ.erase u,
          |unmatchedProb G w (Finset.univ.erase u) v - unmatchedProb G w Finset.univ v| =
        1 - unmatchedProb G w Finset.univ u) ∧
    ∀ S : Finset V,
      ∑ v ∈ Finset.univ \ S,
          |unmatchedProb G w (Finset.univ \ S) v - unmatchedProb G w Finset.univ v| ≤
        (S.card : ℝ) := by sorry

end SubexpPermanent.Main
