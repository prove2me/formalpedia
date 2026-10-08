-- Prove2me | Theorems.Thm_P7ThreeColor_Seed_corollary_5
-- name    : P7ThreeColor.Seed.corollary_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:03.564411+00:00
-- url     : https://prove2.me/theorems/e07abd26-fcdc-4efd-b1b9-63f7f434bf81
-- title:
--   Corollary 5, p. 6 — a small connected 2-dominating set or a K₄
-- statement:
--   Let $G$ be a finite connected simple graph with no induced path on seven vertices. Then $G$ has a connected 2-dominating set of at most three vertices or contains a complete subgraph on four vertices:
--
--   $$
--   \bigl(\exists S\subseteq V(G):\ |S|\le 3,\ G[S]\text{ connected},\ \overline{\bar S}=V(G)\bigr)
--   \quad\lor\quad K_4\subseteq G.
--   $$
--
--   The result supplies a small structural seed for the paper's graph-coloring analysis whenever the $K_4$ obstruction is absent.
--
--   **Formalization Note** The paper's second sentence, which gives a running time for finding the set or subgraph, is outside this statement because no machine model is part of the mission. A complete subgraph of four vertices is represented by `¬ G.CliqueFree 4`; the disjunction is inclusive.
-- source:
--   Bonomo, Chudnovsky, Maceli, Schaudt, Stein and Zhong, Three-coloring and list three-coloring of graphs without induced paths on seven vertices, Combinatorica (2017), DOI 10.1007/s00493-017-3553-8, p. 6, Corollary 5, first sentence

import Mathlib
import Definitions.Def_P7ThreeColor_Seed_Basic

namespace P7ThreeColor.Seed

/-- First statement of Corollary 5, p. 6. -/
theorem corollary_5 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (h7 : PFree 7 G) :
    (∃ S : Finset V, S.card ≤ 3 ∧ (G.induce (S : Set V)).Connected ∧
      IsTwoDominating G S) ∨ ¬ G.CliqueFree 4 := by sorry

end P7ThreeColor.Seed
