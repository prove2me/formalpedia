-- Prove2me | Theorems.Thm_TranspositionIID_Main_lemma_3_2
-- name    : TranspositionIID.Main.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:52.601714+00:00
-- url     : https://prove2.me/theorems/73687343-5852-4b9e-ba7f-1693879246ed
-- title:
--   Lemma 3.2 — biased exclusion inversion count
-- statement:
--   Let $n\ge1024$, $2\le N\le n$ and $0<\theta\le1/2$. Start the biased exclusion chain of Definition 3.1 at any binary word $Y_0$ containing positive fixed numbers of both letters. Then
--   $$\mathbb E[V(Y_{n^4})]\le\frac14+\frac{\pi^2}{6\theta^2}.$$
--   The result is uniform over the starting word and both positive letter counts.
--
--   Differences from the source:
--   - encoding: binary words in a fixed positive-count class → the count-preserving kernel on all words, started at any word with both letters; reason: each such trajectory stays in exactly one source state space and every fixed-count start is included
--   - encoding: positions 1 through N and the n to the fourth step → Fin N positions and the finite matrix power n ^ 4; reason: shifting positions preserves adjacency and inversion order; the row of the matrix power is the chain law
-- source:
--   Clayton Mizgerd, Transposition achieves OPT+O(1) in polynomial time for IID list update, STOC 2027 submission #668 (October 2026), supplied canonical submission artifact; citation basis published (not acceptance). Lemma 3.2, printed p.5 = PDF p.5; source.pdf SHA256 07dbf227a79b9907070bc1c27f25a0848cee3135ec65bcf105159f991b3b4545.

import Definitions.Def_TranspositionIID_Main_Exclusion

namespace TranspositionIID.Main

/-- Lemma 3.2, printed/PDF p.5. Both letter counts are positive initially and preserved. -/
theorem lemma_3_2 (n N : ℕ) (hn : 1024 ≤ n) (hN : 2 ≤ N) (hNn : N ≤ n)
    (θ : ℝ) (hθ : 0 < θ) (hθcap : θ ≤ 1 / 2) (w : BinaryWord N)
    (hL : ∃ i, w i = false) (hH : ∃ i, w i = true) :
    expectedAfter (exclusionKernel N θ) w (n ^ 4) binaryInversions ≤
      1 / 4 + Real.pi ^ 2 / (6 * θ ^ 2) := by sorry

end TranspositionIID.Main
