-- Prove2me | Theorems.Thm_PoSUndirected_lemma_A_1_properness
-- name    : PoSUndirected.lemma_A_1_properness
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:39.663209+00:00
-- url     : https://prove2.me/theorems/4533d17f-0f30-439a-ba4a-1c9d77e39cec
-- title:
--   Lemma A.1 — at a weak equilibrium any two player paths have acyclic union, and used edges are used by their owners
-- statement:
--   Let $G=(V,E)$ be a finite undirected loopless multigraph with positive edge costs $c_e>0$, and consider a network design game on $G$ in which every player may choose any simple path between her terminals. Let $A$ be a weak equilibrium. Then:
--
--   1. for any two players $i,j$ the union $A_i\cup A_j$ is acyclic;
--   2. consequently, their subpaths between any two common vertices coincide: if $P\subseteq A_i$ and $Q\subseteq A_j$ are both simple $v$–$w$ paths, then $P=Q$;
--   3. every used edge is used directly by its owner: if player $i$ is an endpoint owner of $e$ and $\ell_e(A)>0$, then $A_i=\{e\}$;
--   4. a nondirect owner's edge is unused: if $i$ owns $e$ and $A_i\neq\{e\}$, then $\ell_e(A)=0$;
--   5. all external crossers of a two-attachment region $R$ use the same actual internal path: $A_i\cap R=A_j\cap R$ for any two of them.
--
--   This properness lemma reduces an equilibrium to a family of pairwise compatible routes and is the first step of the local analysis of the lower construction.
--
--   **Formalization Note** An external crosser is a player with no terminal strictly inside $R$ whose path uses an edge of $R$; a two-attachment region with attachments $p,q$ is an edge set meeting the rest of the graph only at $p$ and $q$.
--
--   Differences from the source:
--   - generalization: "In an owned-edge game, every used edge is used directly by its owner" → stated for every player that is an endpoint owner of an edge, in any game of the §2 model; reason: an owned-edge game is the case in which every edge has such a player
--   - generalization: external crossers of a region (players owning an edge outside it) → players with no strictly internal terminal whose path uses an edge of the region; reason: a player owning an edge outside the region has no strictly internal terminal (p.13), so the source's crossers are among them
--   - generalization: a region meeting the rest of the graph at exactly two vertices → at most the two vertices $p,q$; reason: contains the two-vertex case
--   - generalization: terminals of each player in one connected component → not assumed; reason: a player without a path has no strategy, so no equilibrium exists and the statement is vacuous there
--   - encoding: subpaths between two common vertices coincide → any two simple $v$–$w$ paths contained in the two player paths are equal; reason: the subpath of a simple path between two of its vertices is the unique simple $v$–$w$ path inside it
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), Lemma A.1, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_PoSUndirected_ndGame

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace PoSUndirected

/-- Tsoufis, *The Price of Stability in Undirected Network Design: Lower Bounds and Structural
Guarantees* (preprint, sha256 c095d811…), Lemma A.1 (Properness and used edges), p.13 (PDF p.15).
In every weak equilibrium `A` of a network design game on a finite loopless multigraph with
positive edge costs:

1. the union of any two player paths is acyclic;
2. their subpaths between any two common vertices coincide (two simple `v`–`w` paths contained
   in two player paths are equal);
3. in an owned-edge game every used edge is used directly by its owner;
4. a nondirect owner's edge is unused;
5. all external crossers of a two-attachment region use the same actual internal path.

**Formalization Note.** Clauses 3–4 are stated for every player `i` that is an endpoint owner
of an edge `e` in an arbitrary game of the §2 model, which contains the owned-edge games. An
external crosser of the region `R` with attachments `p`, `q` is a player with no terminal
strictly inside `R` whose path uses an edge of `R` (`IsCrosser`); this contains every player
owning an edge outside `R`. -/
theorem lemma_A_1_properness {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] [Fintype ι] [DecidableEq ι] (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (c : E → ℝ) (hc : ∀ e, 0 < c e) (s t : ι → V)
    (A : ι → Finset E) (hA : IsPureNash (ndGame ends c s t) A) :
    (∀ i j : ι, IsAcyclicEdges ends (A i ∪ A j)) ∧
    (∀ (i j : ι) (v w : V) (P Q : Finset E), P ⊆ A i → Q ⊆ A j →
      IsSimplePathEdges ends v w P → IsSimplePathEdges ends v w Q → P = Q) ∧
    (∀ (i : ι) (e : E), IsEndpointOwner ends s t i e → 0 < load A e → A i = {e}) ∧
    (∀ (i : ι) (e : E), IsEndpointOwner ends s t i e → A i ≠ {e} → load A e = 0) ∧
    (∀ (R : Finset E) (p q : V), IsTwoAttachment ends R p q → ∀ i j : ι,
      IsCrosser ends s t R p q A i → IsCrosser ends s t R p q A j → A i ∩ R = A j ∩ R) := by sorry

end PoSUndirected
