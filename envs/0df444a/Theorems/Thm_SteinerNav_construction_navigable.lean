-- Prove2me | Theorems.Thm_SteinerNav_construction_navigable
-- name    : SteinerNav.construction_navigable
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:47:32.560805+00:00
-- url     : https://prove2.me/theorems/09cee49c-1f06-4413-96b7-1dec10d519f1
-- title:
--   Proof of Theorem 3, p.9 — if all landmark covers succeed, the three-type graph is Steiner $\alpha$-navigable with no Steiner-to-Steiner edges
-- statement:
--   Let $\alpha>1$, let $P\subset\mathbb R^d$ be finite, let $Q\subseteq P$ be a nonempty set of landmarks, and let $S$ be a finite set of sampled locations such that, for every landmark $q\in Q$, $S$ $\alpha$-covers $P$ with respect to $q$ (all landmark covers succeed). Let $R=S\setminus P$ and let $G$ be the graph on $P\cup R$ with the three edge types of Theorem 3's construction (no self-loops). Then
--
--   1. $G$ is an $\alpha$-navigable graph with Steiner points $R$ for $P$;
--   2. $G$ has no self-loops;
--   3. $G$ has no Steiner-to-Steiner edges.
--
--   This is the deterministic half of Theorem 3: navigability needs only that the landmark covers succeed, not how they were obtained.
--
--   Differences from the source:
--   - generalization: α = 1 + 1/d and S the union of the random candidates of Corollary 4.2 → any α > 1 and any finite S that α-covers P with respect to every landmark; reason: the page's argument uses only the covers and Observation 4.3; the paper's situation is the special case α = 1 + 1/d on the event that all covers succeed.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee6…), proof of Theorem 3, p.9 (first paragraph); edge types, p.8

import Mathlib
import Definitions.Def_SteinerNav_IsSteinerNavigable
import Definitions.Def_SteinerNav_constructionEdges

namespace SteinerNav

/-- Proof of Theorem 3, navigability: if `S` `α`-covers `P` with respect to each landmark of a nonempty
`Q ⊆ P`, the three-type graph is an `α`-navigable graph with Steiner points `R = S \ P`, without
self-loops and without Steiner-to-Steiner edges (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), proof of Theorem 3, p.9). -/
theorem construction_navigable {d : ℕ} (α : ℝ) (hα : 1 < α) (P Q S : Finset (Pt d))
    (hQ : Q.Nonempty) (hQP : Q ⊆ P) (hS : ∀ q ∈ Q, CoversSet α q S P) :
    IsSteinerNavigable α P (S \ P) (constructionEdges P Q S) ∧
      (∀ x, (x, x) ∉ constructionEdges P Q S) ∧
      NoSteinerToSteiner (S \ P) P (constructionEdges P Q S) := by sorry

end SteinerNav
