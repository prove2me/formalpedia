-- Prove2me | Theorems.Thm_RankingBeats_General_section_5_identity
-- name    : RankingBeats.General.section_5_identity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:27:25.08772+00:00
-- url     : https://prove2.me/theorems/bbf62295-57e2-4b5c-8bc8-7f152bcc143d
-- title:
--   §5 display (p. 16) — with a perfect matching, the approximation ratio equals Pr[a uniform random vertex is matched]
-- statement:
--   Let $G=(V,E)$ be a finite simple graph that contains a perfect matching $\mathrm{OPT}$, and let the ranks be i.i.d. uniform on $[0,1)$. Then $|\mathrm{OPT}|=\nu(G)=|V|/2$, and the approximation ratio $\alpha=\mathbb E_{\vec x}[|R(\vec x)|]/|\mathrm{OPT}|$ satisfies
--   $$\alpha=\frac{\tfrac12\,\mathbb E_{\vec x}\big[\sum_{v\in V}\mathbf 1\{v\text{ is matched}\}\big]}{|V|/2}=\frac{\sum_{v\in V}\Pr[v\text{ is matched}]}{|V|}=\Pr[u\text{ is matched}],$$
--   where $u$ is a uniform random vertex of $V$, independent of the ranks. This is how the paper reduces the approximation ratio to the probability that a single vertex is matched, the quantity its LP bounds.
--
--   Differences from the source:
--   - encoding: Pr[u is matched] for a uniform random vertex u → probUniformVertexMatched G = Σ_v (1/|V|) · Pr_x[v is matched]; reason: u is uniform on V and independent of x, so this is its probability by the law of total probability
--   - generalization: G = (V, E) with a perfect matching OPT of size |V|/2 (so V is nonempty, as the division by |OPT| requires) → no nonemptiness hypothesis on V; reason: at |V| = 0 every term is 0 under Lean's x/0 = 0, so the statement specializes to the paper's for nonempty V
--   - encoding: Ranking on rank vectors with distinct ranks (ties have probability zero) → ranking is defined on every x : V → ℝ, with ties broken by a fixed [LinearOrder V]; the vertex type carries such an order; reason: every finite type has a linear order, and the tie-break changes R(x) only on a null set, so the expectation is the paper's
-- source:
--   Derakhshan, Yu, Ranking Beats 1-1/e on General Graphs, STOC 2027 submission (manuscript sha256 6715d477…), p. 16, §5, display (opening of §5)

import Mathlib
import Definitions.Def_StochMatchPoly_mu
import Definitions.Def_RankingBeats_General_Ranking

open Classical MeasureTheory

namespace RankingBeats.General

/-- **§5, display on p. 16.** If `G` has a perfect matching, then
`|OPT| = |V|/2` and the approximation ratio `α = E_x[|R(x)|] / |OPT|` satisfies
`α = (1/2 · E_x[∑_{v ∈ V} 1{v is matched}]) / (|V|/2) = (∑_{v ∈ V} Pr[v is matched]) / |V|
= Pr[u is matched]` for a uniform random vertex `u`. -/
theorem section_5_identity {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hpm : ∃ M : G.Subgraph, M.IsPerfectMatching) :
    (StochMatchPoly.mu G.edgeFinset : ℝ) = (Fintype.card V : ℝ) / 2 ∧
    expectedSize G / (StochMatchPoly.mu G.edgeFinset : ℝ) =
      (1 / 2 * ∫ x, (∑ v, if IsMatched (ranking G ∅ x) v then (1 : ℝ) else 0) ∂ rankLaw V) /
        ((Fintype.card V : ℝ) / 2) ∧
    (1 / 2 * ∫ x, (∑ v, if IsMatched (ranking G ∅ x) v then (1 : ℝ) else 0) ∂ rankLaw V) /
        ((Fintype.card V : ℝ) / 2) =
      (∑ v, probMatched G v) / (Fintype.card V : ℝ) ∧
    (∑ v, probMatched G v) / (Fintype.card V : ℝ) = probUniformVertexMatched G := by sorry

end RankingBeats.General
