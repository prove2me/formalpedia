-- Prove2me | Theorems.Thm_SteinerCutDominants_proposition_1
-- name    : SteinerCutDominants.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:59.489789+00:00
-- url     : https://prove2.me/theorems/47a30fd0-b4b9-4b35-a92c-5a5b885ba16f
-- title:
--   Proposition 1: structure of facet inducing Steiner graphs
-- statement:
--   Let $(G,T)$ be facet inducing with facet weights $c$. Then:
--
--   1. $G$ is connected.
--   2. Every node in $V(G)\setminus T$ has degree at least two.
--   3. The facet of $\mathrm{CUT}_+(G,T)$ defined by $cx\ge\gamma_c(G,T)$ is bounded.
--   4. If $\delta(S)$ is a root of $c$, then both $S$ and $V(G)\setminus S$ induce connected subgraphs of $G$.
--   5. Every edge of $G$ is contained in at least one root of $c$.
--   6. For every $v\in V(G)$, each component of $G\setminus v$ contains a terminal from $T$.
--   7. For every $e\in E(G)$ we have $c(e)\le\gamma_c(G,T)$, with equality if and only if $e$ is a bridge.
--
--   These facts are used in all later reductions. Part 1 says in particular that the support graph of a non-trivial facet is connected.
--
--   **Formalization Note** The statement is on unbundled data, so that $G$ is not assumed connected. The hypotheses are: every node has an edge ($V_c=V(G)$), $c>0$, $\gamma_c(G,T)>0$, and the roots span $\mathbb R^{E(G)}$.
--
--   Differences from the source:
--   - generalization: facet weights c, in minimum integer form → any positive real vector c with γ_c > 0 whose roots span ℝ^E; reason: the proof does not use integrality; facet weights satisfy these hypotheses
--   - encoding: G_c = G → hypotheses hV (no node without an edge) and hc (c > 0), with G not assumed connected; reason: a Steiner graph is connected by definition, so Part (1) is about G_c; stating it needs a graph not yet known to be connected
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, Proposition 1, p.5

import Mathlib
import Definitions.Def_SteinerCutDominants_cutDominant
import Definitions.Def_SteinerCutDominants_rootCuts

open Matrix

namespace SteinerCutDominants

/-- **Proposition 1** (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, p.5). For every
facet inducing Steiner graph with facet weights `c`: (1) `G` is connected; (2) every node in
`V(G) \ T` has degree at least two; (3) the facet defined by `c x ≥ γ_c(G, T)` is bounded; (4) if
`δ(S)` is a root, both `S` and `V(G) \ S` induce connected subgraphs; (5) every edge is contained in
a root; (6) for every node `v`, each component of `G \ v` contains a terminal; (7) for every edge
`e`, `c(e) ≤ γ_c(G, T)` with equality iff `e` is a bridge.

**Formalization Note** Stated on unbundled data so that (1) has content: `G` is not assumed connected,
`hV` is the page's `V_c = V(G)` (no node without an edge), and `hc`, `hγ`, `hspan` are `G_c = G`,
`γ > 0` and the root basis. Integrality of `c` is not used. Each hypothesis holds for a
facet inducing `H : WSG` with `c = H.wR`. -/
theorem proposition_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (T : Finset V) (hT : 2 ≤ T.card) (c : G.edgeSet → ℝ)
    (hV : ∀ v, ∃ u, G.Adj v u) (hc : ∀ e, 0 < c e) (hγ : 0 < gammaOf G T c)
    (hspan : Submodule.span ℝ (rootCuts G T c) = ⊤) :
    G.Connected ∧
    (∀ v, v ∉ T → 2 ≤ G.degree v) ∧
    Bornology.IsBounded {x ∈ cutDominant G T | c ⬝ᵥ x = gammaOf G T c} ∧
    (∀ S : Finset V, IsRootOf G T c S →
      (G.induce (S : Set V)).Connected ∧ (G.induce ((S : Set V)ᶜ)).Connected) ∧
    (∀ e : G.edgeSet, ∃ S : Finset V, IsRootOf G T c S ∧ cutVec G S e = 1) ∧
    (∀ (v : V) (C : (G.induce ({v}ᶜ : Set V)).ConnectedComponent),
      ∃ x : ({v}ᶜ : Set V), x.1 ∈ T ∧ (G.induce ({v}ᶜ : Set V)).connectedComponentMk x = C) ∧
    (∀ e : G.edgeSet, c e ≤ gammaOf G T c ∧ (c e = gammaOf G T c ↔ G.IsBridge e.1)) := by sorry

end SteinerCutDominants
