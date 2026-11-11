-- Prove2me | Theorems.Thm_SingleExpBisect_Main_lemma_3_2
-- name    : SingleExpBisect.Main.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:40:38.505633+00:00
-- url     : https://prove2.me/theorems/a78d5074-2ff1-46d2-8111-db4a7585edce
-- title:
--   Lemma 3.2 — complement symmetry Z_t = Z_t^{≤2k}(y,w) + (Π y_v) Z_t^{≤2k}(y^{-1},w) at large unbreakable bags
-- statement:
--   Let $B\subseteq W\subseteq V(G)$ (playing $B_t\subseteq V(G_t)$), $k\ge0$, $|B|>4k+1$, and $B$ $(2k,k)$-edge-unbreakable in $G$. Then, as Laurent polynomials,
--   $$Z_t(y,w)=Z_t^{\le2k}(y,w)+\Big(\prod_{v\in V(G_t)}y_v\Big)Z_t^{\le2k}(y^{-1},w).$$
--
--   Differences from the source:
--   - reading: Lemma 3.2's sentence carries no hypothesis → |B| > 4k + 1 and B (2k,k)-edge-unbreakable in G; reason: the paragraph before the lemma (p. 18) fixes this setting ("We now assume that |B_t| > 4k+1", "By the edge-unbreakability guarantee") and the proof uses both
--   - generalization: W = V(G_t), B = B_t for a node of the Section 3 decomposition → any B ⊆ W ⊆ V(G); reason: the proof uses only µ_t(V(G_t) \ A_t) = µ_t(A_t), the unbreakability of B_t and |B_t| > 4k+1; the source's case is a special case
--   - encoding: y^{−1} := (y_v^{−1}) → Laurent polynomials; invY negates every vertex-variable exponent; yProdL W is Π_{v∈W} y_v; reason: the same identity in the Laurent ring
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §3.2, p. 19, Lemma 3.2 (setting p. 18)

import Mathlib
import Definitions.Def_MinBisectFPT_IsUnbreakableTD
import Definitions.Def_SingleExpBisect_Main_NodeData

open scoped Classical

namespace SingleExpBisect.Main

open MinBisectFPT

/-- Kumabe, *Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New
Unbreakable Decomposition*, arXiv:2611.05982 (October 2026), §3.2, p. 19, Lemma 3.2 (in the setting
of p. 18: `|B_t| > 4k + 1` and `B_t` (2k, k)-edge-unbreakable in `G`):
`Z_t(y, w) = Z_t^{≤2k}(y, w) + (Π_{v ∈ V(G_t)} y_v) · Z_t^{≤2k}(y^{−1}, w)` as Laurent polynomials,
with `W = V(G_t)` and `B = B_t ⊆ W`. -/
theorem lemma_3_2 {n : ℕ} (G : SimpleGraph (Fin n)) (W B : Finset (Fin n)) (hBW : B ⊆ W) (k : ℕ)
    (hB : 4 * k + 1 < B.card) (hunb : IsEdgeUnbreakable G Finset.univ B (2 * k) k) :
    toL (Zfull G W k) = toL (Zle G W B k) + yProdL W * invY (toL (Zle G W B k)) := by sorry

end SingleExpBisect.Main
