-- Prove2me | Theorems.Thm_PivotADO_OneHop_lemma_6
-- name    : PivotADO.OneHop.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:56.991479+00:00
-- url     : https://prove2.me/theorems/eb55ea15-6723-4fff-b6b6-827b7f2b7e90
-- title:
--   Lemma 6 — local tree structure and all sphere counts
-- statement:
--   Let $G$ be a finite $d$-regular graph of finite girth $g$, put $h=\lfloor g/2\rfloor-1$, and fix any reversal-consistent shortest-path system $P$. For every vertex $u$ and integer $0\le R\le h$, the induced closed ball $G[B_R(u)]$ is a tree; any vertex $v$ at distance $R$ has a unique shortest path from $u$; and, for $R\ge1$,
--
--   $$|\{v:\delta_G(u,v)=R\}|=d(d-1)^{R-1}.$$
--
--   Moreover, for every $a\ne b$ and integer $R\ge0$ with $\delta_G(b,a)+R\le h$,
--
--   $$|\{v:\delta_G(a,v)=R,\ a\in P(b,v)\}|=(d-1)^R.$$
--
--   This is the local counting interface for high-girth regular graphs. All four conclusions are in one item; no hypothesis $d\ge3$ or oracle is imposed. Uniqueness is expressed as existence of exactly one walk of length $R$, hence identifies the path selected by $P$.
--
--   Differences from the source:
--   - encoding: a finite vertex set V → an arbitrary Fintype V with classical equality and adjacency decisions; reason: finite relabeling and decidability choices change no graph
--   - encoding: finite girth g and shortest-path distance, infinite between components → G.egirth = (g : ℕ∞) and G.edist; weighted distances use ENat.toENNReal; reason: acyclic and disconnected inputs retain their infinite values
--   - encoding: unique shortest path and the induced closed ball → unique walk of length R and the induced set {v | edist u v ≤ R}; reason: at distance R these walks are exactly shortest paths; the explicit non-strict inequality matches the source closed ball
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), Lemma 6, p.6–7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Definitions.Def_PivotADO_OneHop_PathSystem

set_option autoImplicit false
open scoped Classical

namespace PivotADO.OneHop

/-- Lemma 6, Kadria–Roditty, STOC 2027 submission #584 (October 2026), pp.6–7.
All four clauses are retained. No lower bound on d is added. -/
theorem lemma_6 {V : Type*} [Fintype V] (G : SimpleGraph V) (d g : ℕ)
    (hd : G.IsRegularOfDegree d) (hg : G.egirth = (g : ℕ∞)) (P : PathSystem G) :
    (∀ (u : V) (R : ℕ), R ≤ treeRadius g →
      (G.induce {v | G.edist u v ≤ (R : ℕ∞)}).IsTree ∧
      (∀ v : V, G.edist u v = (R : ℕ∞) → ∃! p : G.Walk u v, p.length = R) ∧
      (1 ≤ R → Nat.card {v : V // G.edist u v = (R : ℕ∞)} = d * (d - 1) ^ (R - 1))) ∧
    (∀ (a b : V) (R : ℕ), a ≠ b →
      G.edist b a + (R : ℕ∞) ≤ (treeRadius g : ℕ∞) →
      Nat.card {v : V // G.edist a v = (R : ℕ∞) ∧
        ∃ h : G.Reachable b v, a ∈ (P.path b v h).support} = (d - 1) ^ R) := by sorry

end PivotADO.OneHop
