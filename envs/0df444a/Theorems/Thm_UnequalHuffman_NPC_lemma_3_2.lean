-- Prove2me | Theorems.Thm_UnequalHuffman_NPC_lemma_3_2
-- name    : UnequalHuffman.NPC.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:45:10.968379+00:00
-- url     : https://prove2.me/theorems/7284f6cd-6585-4906-bbd1-66c22a094484
-- title:
--   Lemma 3.2 — the first reduction: Planar Independent Set to the leaf-profile problem with OPT = C − α(G)
-- statement:
--   There are a constant $c$ and a polynomial-time computable map $f$ on strings over `BSym` such that for every simple planar graph $G$ on $n$ vertices, $f$ maps the binary code of $G$ to the code of a well-formed leaf-profile instance $I$ (feasible profile, $n_H > 0$, $N \ge 2$, nonincreasing integer coefficient rows) followed by an integer $C$, with
--   $$\min_T \mathrm{score}(T) = C - \alpha(G),$$
--   height $H \le c(n+1)^4$ and $N \le c(n+1)^5$ leaves. Here $\alpha(G)$ is the independence number (Mathlib `SimpleGraph.indepNum`) and planarity is `WilliamsonShmoys.HasPlanarDrawingOn`.
--
--   Source (p. 30): "Lemma 3.2. Given $G$, one can construct in polynomial time a feasible leaf profile and nonincreasing integer coefficient lists for which $\min_T \mathrm{score}(T) = C - \alpha(G)$, where $C$ is a computable integer. The instance has height $H = O(n^4)$, has $N = O(n^5)$ leaves, and has polynomial binary encoding length."
--
--   Differences from the source:
--   - encoding: given G, construct in polynomial time an instance and a computable integer C → one CookPvsNP.PolyTimeComputable map f with f (graphCode G) = I.code ++ encInt C; reason: the published polynomial-time notion on one-tape machines; C is part of the output
--   - encoding: H = O(n^4), N = O(n^5) → ∃ c fixed before G: H ≤ c (n + 1)^4 and N ≤ c (n + 1)^5; reason: n + 1 covers n = 0; equivalent to the O-bounds for n ≥ 1
--   - encoding: polynomial binary encoding length → not a separate clause: the output of the polynomial-time map f has polynomial length; reason: a Turing machine writes at most one symbol per step
--   - encoding: a feasible leaf profile and nonincreasing integer coefficient lists → I.IsValid: feasible profile, n_H > 0, N ≥ 2, rows nonincreasing; reason: n_H > 0 and N ≥ 2 are part of the leaf-profile problem's input definition (p. 8)
--   - encoding: min_T score(T) = C − α(G); simple planar graph G → I.IsOptTree (C − α(G)) (attained minimum); G : SimpleGraph (Fin n) with HasPlanarDrawingOn, α = indepNum; reason: published planarity definition, Mathlib independence number
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, p. 30, Lemma 3.2

import Mathlib
import Definitions.Def_UnequalHuffman_NPC_LeafProfile
import Definitions.Def_UnequalHuffman_NPC_GraphCode
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open CookPvsNP ProjSchedTW.Complexity

namespace UnequalHuffman.NPC

/-- Lemma 3.2 (p. 30): there are a constant `c` and one polynomial-time computable map on
strings that sends the code of every simple planar graph `G` on `n` vertices to the code of a
leaf-profile instance `I` (feasible profile, `n_H > 0`, `N ≥ 2`, nonincreasing integer rows)
followed by an integer `C` with `min_T score(T) = C - α(G)`, height `H ≤ c (n + 1)^4` and
`N ≤ c (n + 1)^5` leaves (polynomial encoding length follows from polynomial time). -/
theorem lemma_3_2 :
    ∃ c : ℕ, ∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), WilliamsonShmoys.HasPlanarDrawingOn G →
        ∃ (I : LPInstance) (C : ℤ),
          f (graphCode G) = I.code ++ encInt C ∧
          I.IsValid ∧
          I.IsOptTree (C - (G.indepNum : ℤ)) ∧
          I.length ≤ c * (n + 1) ^ 4 ∧
          I.numLeaves ≤ c * (n + 1) ^ 5 := by sorry

end UnequalHuffman.NPC
