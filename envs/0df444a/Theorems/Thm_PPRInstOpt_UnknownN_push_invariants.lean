-- Prove2me | Theorems.Thm_PPRInstOpt_UnknownN_push_invariants
-- name    : PPRInstOpt.UnknownN.push_invariants
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:12:45.092111+00:00
-- url     : https://prove2.me/theorems/b14afe44-41ca-41fc-a910-f3cb1a5a6dea
-- title:
--   §2.1 Eq. (5) and §2.2 Eq. (6) — the forward and backward push invariants
-- statement:
--   Let $G$ be a valid graph and $\alpha\in(0,1)$. Start from $(p_f,r_f)=(0,\mathbf 1_s)$ and apply forward pushes at any finite sequence of vertices, in any order; start from $(p_b,r_b)=(0,\mathbf 1_t)$ and apply backward pushes at any finite sequence of vertices. Then for every vertex $v$ and every vertex $u$
--   $$\pi(s,v)=p_f(v)+\sum_{u\in V}r_f(u)\,\pi(u,v),\qquad \pi(u,t)=p_b(u)+\sum_{v\in V}\pi(u,v)\,r_b(v).$$
--   These invariants ([ACL06, Lemma 1], [ABC+08, Lemma 1]) are what makes the push estimates and the TriPPR estimator unbiased.
--
--   Differences from the source:
--   - encoding: π(u, v) = probability that the α-discounted walk from u terminates at v → ppr α G u v = Σ_k α(1−α)^k P^k(u, v); reason: the paper's own equivalent form (p. 3); same values
--   - encoding: directed simple graph with every out-degree ≥ 1 and fixed adjacency lists → Digraph V over an arbitrary vertex type: duplicate-free out- and in-lists describing one edge set, no self-loops, nonempty out-lists; reason: same instances; list order fixes out(v, i) and in(v, i)
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 12-13, §2.1 Eq. (5), §2.2 Eq. (6)

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_Push

namespace PPRInstOpt.UnknownN

/-- §2.1 Eq. (5) and §2.2 Eq. (6): starting from `(p_f, r_f) = (0, 1_s)`, after any finite
sequence of forward pushes `π(s, v) = p_f(v) + Σ_u r_f(u) π(u, v)` for every `v`; starting from
`(p_b, r_b) = (0, 1_t)`, after any finite sequence of backward pushes
`π(u, t) = p_b(u) + Σ_v π(u, v) r_b(v)` for every `u`. -/
theorem push_invariants {V : Type} [Fintype V] [DecidableEq V] (α : ℝ) (hα0 : 0 < α)
    (hα1 : α < 1) (G : Digraph V) (s t : V) (Lfwd Lbwd : List V) :
    (∀ v : V,
      ppr α G s v = (Lfwd.foldl (fwdPush G.oracle α) (fwdStart s)).1 v +
        ∑ u : V, (Lfwd.foldl (fwdPush G.oracle α) (fwdStart s)).2 u * ppr α G u v) ∧
    (∀ u : V,
      ppr α G u t = (Lbwd.foldl (bwdPush G.oracle α) (bwdStart t)).1 u +
        ∑ v : V, ppr α G u v * (Lbwd.foldl (bwdPush G.oracle α) (bwdStart t)).2 v) := by sorry

end PPRInstOpt.UnknownN
