-- Prove2me | Theorems.Thm_P7ThreeColor_Seed_theorem_4
-- name    : P7ThreeColor.Seed.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:48.712083+00:00
-- url     : https://prove2.me/theorems/99c92b78-80e9-4825-b57a-933ab011e9fe
-- title:
--   Theorem 4 (Camby and Schaudt, cited), p. 6 — connected domination in Pₜ-free graphs
-- statement:
--   Let $t\ge 3$, and let $G$ be a finite connected graph with no induced path on $t$ vertices. There is a connected dominating set $S$ such that the graph induced by $S$ is either $P_{t-2}$-free or isomorphic to $P_{t-2}$:
--
--   $$
--   \exists S\subseteq V(G):\quad \bar S=V(G),\quad G[S]\text{ is connected},\quad
--   \bigl(G[S]\text{ is }P_{t-2}\text{-free}\;\lor\;G[S]\cong P_{t-2}\bigr).
--   $$
--
--   This cited structural result is applied twice in the proof of Corollary 5, first with $t=7$ and then with $t=5$.
--
--   **Formalization Note** The lower bound $t\ge 3$ makes natural-number subtraction in $t-2$ agree with the paper. Connectedness includes nonemptiness.
-- source:
--   Bonomo, Chudnovsky, Maceli, Schaudt, Stein and Zhong, Three-coloring and list three-coloring of graphs without induced paths on seven vertices, Combinatorica (2017), DOI 10.1007/s00493-017-3553-8, p. 6, Theorem 4 (citing Camby and Schaudt [2])

import Mathlib
import Definitions.Def_P7ThreeColor_Seed_Basic

namespace P7ThreeColor.Seed

/-- Camby and Schaudt's result, cited as Theorem 4 on p. 6. -/
theorem theorem_4 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (t : ℕ) (ht : 3 ≤ t)
    (hG : G.Connected) (hP : PFree t G) :
    ∃ S : Finset V, IsDominating G S ∧ (G.induce (S : Set V)).Connected ∧
      (PFree (t - 2) (G.induce (S : Set V)) ∨
        Nonempty (G.induce (S : Set V) ≃g SimpleGraph.pathGraph (t - 2))) := by sorry

end P7ThreeColor.Seed
