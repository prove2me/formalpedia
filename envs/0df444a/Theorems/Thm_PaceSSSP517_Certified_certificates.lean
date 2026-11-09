-- Prove2me | Theorems.Thm_PaceSSSP517_Certified_certificates
-- name    : PaceSSSP517.Certified.certificates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:02:45.152554+00:00
-- url     : https://prove2.me/theorems/880eb6c6-4242-4c6f-9c2f-9d625c96b69d
-- title:
--   Lemma 3.2 — Exactness and every nonempty window certificate
-- statement:
--   At any actual round $r$, whatever the fresh sample did, the following statements hold. If $W_r=0$, then $d_r=\operatorname{dist}_G$ and $T_r$ is an exact shortest-path tree of the whole graph. For every nonempty subset $S\subseteq\{1,\ldots,r\}$ and every vertex $x$,
--
--   $$d_r(x)\le\frac1{|S|}\sum_{j\in S}d_j(x)
--   \le(1+\kappa_S)\operatorname{dist}_G(s_0,x),\qquad
--   \kappa_S=\max_{e\in E}\frac1{|S|}\sum_{j\in S}J(e;d_j).$$
--
--   This certifies the current tree using any chosen nonempty subset of the past, including all tested suffixes and the full history. Both the exactness and approximation clauses are deterministic; neither is conditioned on the high-probability sampling event. It is this statement that makes the actual stopping test sound on every trajectory.
--
--   Differences from the source:
--   - encoding: finite undirected positive-real weighted graphs and one-based rounds → Fin n vertices, each edge stored once with its smaller endpoint first, and list position j-1 for round j; source vertex s₀ and real sample budget s; reason: these are bijective naming and indexing conventions; no parallel edges or weight restriction is added
--   - encoding: compute exact source distances and a shortest-path tree of the observed subgraph → n-1 synchronous local Bellman–Ford relaxations and the least numbered tight predecessor at each non-source vertex; reason: this fixes a permitted deterministic tie rule using only the observed subgraph; its exactness and finite path realization are proof obligations, not run assumptions
--   - encoding: a maximum over edges and a nonempty subset of past rounds → a finite maximum with an additional zero candidate; only nonempty in-range windows occur in the theorem; reason: relative jumps are nonnegative, so adjoining zero leaves the edge maximum unchanged; the extra zero only defines an unused empty-edge case
--   - generalization: the current fresh sample is drawn from the prescribed Bernoulli kernel → the deterministic certificate holds for every subset F of E, including subsets of conditional probability zero; reason: every supported current sample is included, and soundness applies to the local subgraph for any such subset without a probabilistic premise
-- source:
--   Sarwan Ali, STOC 2027 submission #517 (October 2026), p. 7, Lemma 3.2(a–b); p. 17, Appendix A.2

import Definitions.Def_PaceSSSP517_Certified_Algorithm

set_option autoImplicit false
open scoped ENNReal NNReal

namespace PaceSSSP517.Certified

/-- Lemma 3.2, p.7; proof A.2 p.17. No probabilistic premise, and all
nonempty subsets of past rounds rather than only the tested suffixes. -/
theorem certificates
    (n k : ℕ) (ε : ℝ) (G : WeightedGraph n) (H : Finset (Edge n))
    (s₀ : Fin n)
    (hparams : Parameters n k ε) (hG : Connected G.edges)
    (hH : IsSpanner G H (2 * (k : ℝ) - 1 + ε))
    (a : State n) (ha : PreHistory G H s₀ k ε a)
    (F : Finset (Edge n)) (hF : F ⊆ G.edges) :
    let b := advance G H s₀ k ε a F
    let r := a.rounds.length + 1
    let t := roundAt b.rounds r
    (violatingWeight G a t.d = 0 →
      (∀ x, t.d x = distance G G.edges s₀ x) ∧ IsShortestTree G G.edges s₀ t.tree) ∧
    (∀ S : Finset ℕ, S.Nonempty → S ⊆ past r → ∀ x : Fin n,
      t.d x ≤ windowAverage b.rounds S x ∧
      windowAverage b.rounds S x ≤ (1 + kappa G b.rounds S) * distance G G.edges s₀ x) := by sorry

end PaceSSSP517.Certified
