-- Prove2me | Theorems.Thm_P7ThreeColor_Lemma11_X_no_nbr_in_S
-- name    : P7ThreeColor.Lemma11.X_no_nbr_in_S
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:49.287621+00:00
-- url     : https://prove2.me/theorems/f90f3d30-def2-4dc5-b679-c11b35b77315
-- title:
--   §3.1, p. 15 — no vertex of X has a neighbor in S
-- statement:
--   Let $G$, $L$ and $S$ satisfy the hypotheses of Lemma 11, and let $X$ be the set of vertices with $|L(v)| = 3$. Then
--
--   $$\text{no vertex of } X \text{ is adjacent to a vertex of } S.$$
--
--   Together with the anticompleteness hypothesis of Lemma 11, this confines the neighborhood of each $x \in X$ to $N(S) \cup X$, and since $X$ is stable, to $N(S)$.
-- source:
--   Bonomo, Chudnovsky, Maceli, Schaudt, Stein and Zhong, Three-coloring and list three-coloring of graphs without induced paths on seven vertices, Combinatorica (2017), DOI 10.1007/s00493-017-3553-8, p. 15, §3.1, second paragraph ("By the same hypothesis, no vertex of X has neighbors in S.")

import Mathlib
import Definitions.Def_P7ThreeColor_Lemma11_Setting

namespace P7ThreeColor.Lemma11

/-- p. 15: under the hypothesis of Lemma 11, no vertex of `X` has a neighbor in `S`. -/
theorem X_no_nbr_in_S {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (L : V → Finset (Fin 3)) (S : Finset V) (hyp : Lemma11Hyp G L S)
    (x s : V) (hx : x ∈ X L) (hs : s ∈ S) :
    ¬ G.Adj x s := by sorry

end P7ThreeColor.Lemma11
