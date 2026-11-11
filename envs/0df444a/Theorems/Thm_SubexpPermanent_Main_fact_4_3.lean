-- Prove2me | Theorems.Thm_SubexpPermanent_Main_fact_4_3
-- name    : SubexpPermanent.Main.fact_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:01:25.864901+00:00
-- url     : https://prove2.me/theorems/81ed4de3-f17c-4223-9a6f-987571dcedf0
-- title:
--   Fact 4.3 — deletion recursion: $q_G(u)=Z(G-u)/Z(G)=(1+\sum_v w_{uv}q_{G-u}(v))^{-1}$, $\mu_{uv}=w_{uv}q_G(u)q_{G-u}(v)$, $\log Z(G)=-\sum_j\log q_{G_j}(u_j)$
-- statement:
--   Let $G=(V,E)$ be a finite simple graph with positive edge weights $w$, and write $Z(H)$ for the matching partition function of a subgraph $H$ (with the same weights) and $q_H(u)$ for the probability that $u$ is unmatched under the matching distribution of $H$. For every vertex $u$,
--   $$q_G(u)=\frac{Z(G-u)}{Z(G)}=\Big(1+\sum_{v\in N_G(u)}w_{uv}\,q_{G-u}(v)\Big)^{-1},\qquad \mu_{w,uv}=w_{uv}\,q_G(u)\,q_{G-u}(v)\quad(uv\in E).$$
--   For every ordering $u_1,\dots,u_N$ of $V$, with $G_j=G-\{u_1,\dots,u_{j-1}\}$,
--   $$\log Z(G)=-\sum_{j=1}^{N}\log q_{G_j}(u_j).$$
--   This recursion is the basis of the deterministic counting algorithm (Theorem 7.1). It expresses unmatched probabilities through smaller graphs, and $\log Z$ through unmatched probabilities.
--
--   Differences from the source:
--
--   - encoding: G − S (delete S and its incident edges, keep the other weights) → the subgraph induced on Finset.univ \ S, passed as the vertex-set argument of matchingZ / unmatchedProb / edgeProb; reason: it is the same weighted graph
--   - encoding: an ordering u_1, …, u_N of V and G_j = G − {u_1, …, u_{j−1}} for 1 ≤ j ≤ N → a bijection ord : Fin N ≃ V, 0-based j, removed set {ord i : i < j}; reason: index shift only
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 12, Fact 4.3, eq. (13)

import Mathlib
import Definitions.Def_SubexpPermanent_Main_Matchings

namespace SubexpPermanent.Main

/-- Fact 4.3 (deletion recursion), p. 12. -/
theorem fact_4_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Sym2 V → ℝ) (hw : ∀ e ∈ G.edgeSet, 0 < w e) :
    (∀ u : V,
      unmatchedProb G w Finset.univ u =
          matchingZ G w (Finset.univ.erase u) / matchingZ G w Finset.univ ∧
      unmatchedProb G w Finset.univ u =
          (1 + ∑ v ∈ Finset.univ.filter (G.Adj u),
              w s(u, v) * unmatchedProb G w (Finset.univ.erase u) v)⁻¹ ∧
      ∀ v : V, G.Adj u v →
        edgeProb G w Finset.univ s(u, v) =
          w s(u, v) * unmatchedProb G w Finset.univ u *
            unmatchedProb G w (Finset.univ.erase u) v) ∧
    ∀ ord : Fin (Fintype.card V) ≃ V,
      Real.log (matchingZ G w Finset.univ) =
        -∑ j : Fin (Fintype.card V),
          Real.log (unmatchedProb G w
            (Finset.univ \ (Finset.univ.filter (fun i : Fin (Fintype.card V) => i < j)).image ord)
            (ord j)) := by sorry

end SubexpPermanent.Main
