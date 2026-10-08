-- Prove2me | Theorems.Thm_P7ThreeColor_Seed_dominating_of_dominating
-- name    : P7ThreeColor.Seed.dominating_of_dominating
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:03.707991+00:00
-- url     : https://prove2.me/theorems/8aa04aee-d05f-4406-b296-e09d3b2c5829
-- title:
--   Proof of Corollary 5, p. 6 — domination composes to 2-domination
-- statement:
--   Let $G$ be a finite simple graph, $S$ a dominating vertex set, and $T\subseteq S$ a connected vertex set. Suppose every vertex of $S$ lies in $T$ or has a neighbor in $T$. Then $T$ is connected and 2-dominates $G$:
--
--   $$
--   \overline{\bar T}=V(G).
--   $$
--
--   This is the domination step used when Corollary 5 finds a small connected dominating set inside the graph induced by $S$.
--
--   **Formalization Note** The theorem states the domination implication for any cardinality of $T$; in the paper it is applied when $|T|\le 3$. The hypothesis about vertices of $S$ is precisely domination of $G[S]$ by $T$.
-- source:
--   Bonomo, Chudnovsky, Maceli, Schaudt, Stein and Zhong, Three-coloring and list three-coloring of graphs without induced paths on seven vertices, Combinatorica (2017), DOI 10.1007/s00493-017-3553-8, p. 6, proof of Corollary 5, sentence beginning 'If |S′| ≤ 3'

import Mathlib
import Definitions.Def_P7ThreeColor_Seed_Basic

namespace P7ThreeColor.Seed

/-- Proof of Corollary 5, p. 6: a connected set dominating a dominating set is 2-dominating. -/
theorem dominating_of_dominating {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S T : Finset V)
    (hS : IsDominating G S) (hTS : T ⊆ S)
    (hTdom : ∀ v ∈ S, v ∈ T ∨ ∃ t ∈ T, G.Adj v t)
    (hTconn : (G.induce (T : Set V)).Connected) :
    (G.induce (T : Set V)).Connected ∧ IsTwoDominating G T := by sorry

end P7ThreeColor.Seed
