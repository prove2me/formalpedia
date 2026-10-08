-- Prove2me | Theorems.Thm_P7ThreeColor_Lemma11_list_of_seed_nbr
-- name    : P7ThreeColor.Lemma11.list_of_seed_nbr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:35.903988+00:00
-- url     : https://prove2.me/theorems/42f5c964-9eff-417f-b277-f21c5d766248
-- title:
--   §3.1, p. 15 — a vertex of S adjacent to d ∈ Dᵢ has list {i}
-- statement:
--   Let $G$, $L$ and $S$ satisfy the hypotheses of Lemma 11, and let $D_i$ be the set of vertices $v \in N(S)$ with $L(v) = \{1,2,3\}\setminus\{i\}$. Then for every $d \in D_i$ and every $s \in S$ adjacent to $d$,
--
--   $$L(s) = \{i\}.$$
--
--   This fixes the color of every vertex of $S$ next to $D_i$, and is what makes the inner vertices of the paths in Claim 12 non-adjacent to the "wrong" sets $D_j$.
-- source:
--   Bonomo, Chudnovsky, Maceli, Schaudt, Stein and Zhong, Three-coloring and list three-coloring of graphs without induced paths on seven vertices, Combinatorica (2017), DOI 10.1007/s00493-017-3553-8, p. 15, §3.1, second paragraph ("Observe that, under the hypothesis of Lemma 11, ...")

import Mathlib
import Definitions.Def_P7ThreeColor_Lemma11_Setting

namespace P7ThreeColor.Lemma11

/-- p. 15: under the hypothesis of Lemma 11, for every `d ∈ D_i` and every `s ∈ S ∩ N(d)`,
`L(s) = {i}`. -/
theorem list_of_seed_nbr {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (L : V → Finset (Fin 3)) (S : Finset V) (hyp : Lemma11Hyp G L S)
    (i : Fin 3) (d s : V) (hd : d ∈ D G L S i) (hs : s ∈ S) (hds : G.Adj d s) :
    L s = {i} := by sorry

end P7ThreeColor.Lemma11
