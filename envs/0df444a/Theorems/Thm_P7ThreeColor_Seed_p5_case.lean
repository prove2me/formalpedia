-- Prove2me | Theorems.Thm_P7ThreeColor_Seed_p5_case
-- name    : P7ThreeColor.Seed.p5_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:38.69791+00:00
-- url     : https://prove2.me/theorems/7c44847c-c6cf-4593-b849-4b092b8e1a40
-- title:
--   Proof of Corollary 5, p. 6 — the three inner vertices of a P₅
-- statement:
--   Let $G$ be a finite simple graph and let $S$ be a connected dominating set whose induced subgraph is isomorphic to the path $P_5$. Then there is a connected set $T\subseteq S$ of exactly three vertices that 2-dominates $G$:
--
--   $$
--   |T|=3,\qquad \overline{\bar T}=V(G).
--   $$
--
--   This is the path case in the proof of Corollary 5.
--
--   **Formalization Note** Under the path isomorphism, $T$ is the image of the three non-leaf vertices. The Lean statement asserts the existence of such a set and carries the induced-subgraph isomorphism as a hypothesis.
-- source:
--   Bonomo, Chudnovsky, Maceli, Schaudt, Stein and Zhong, Three-coloring and list three-coloring of graphs without induced paths on seven vertices, Combinatorica (2017), DOI 10.1007/s00493-017-3553-8, p. 6, proof of Corollary 5, P₅ case

import Mathlib
import Definitions.Def_P7ThreeColor_Seed_Basic

namespace P7ThreeColor.Seed

/-- Proof of Corollary 5, p. 6: the inner vertices of an induced `P₅` work. -/
theorem p5_case {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V)
    (hS : IsDominating G S) (hSconn : (G.induce (S : Set V)).Connected)
    (e : G.induce (S : Set V) ≃g SimpleGraph.pathGraph 5) :
    ∃ T : Finset V, T.card = 3 ∧ T ⊆ S ∧
      (G.induce (T : Set V)).Connected ∧ IsTwoDominating G T := by sorry

end P7ThreeColor.Seed
