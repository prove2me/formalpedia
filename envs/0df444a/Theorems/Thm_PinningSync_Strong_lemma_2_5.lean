-- Prove2me | Theorems.Thm_PinningSync_Strong_lemma_2_5
-- name    : PinningSync.Strong.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:24:19.526533+00:00
-- url     : https://prove2.me/theorems/8baf5a2d-dfaa-4238-890c-897ee44ab3f5
-- title:
--   Lemma 2.5, p. 1399 — a matrix with nonnegative off-diagonal entries is irreducible iff its network is strongly connected
-- statement:
--   Let $G$ be a real $N\times N$ matrix with $G_{ij}\ge 0$ for $i\ne j$, and let $\mathcal G$ be its network, which has a directed edge from vertex $j$ to vertex $i\ne j$ exactly when $G_{ij}>0$. Then
--   $$
--   G \text{ is irreducible (Definition 2.4)} \iff \mathcal G \text{ is strongly connected (Definition 2.3)}.
--   $$
--
--   This is the bridge between the matrix hypothesis of Lemmas 2.11–2.12 (irreducibility) and the graph hypothesis of Theorem 3.1 (strong connectivity).
--
--   **Formalization Note.** The paper states the lemma for "a matrix $G$ and its corresponding network"; it is stated here for the paper's matrices, those with nonnegative off-diagonal entries, for which the corresponding network is defined on p. 1397. Diagonal entries play no role.
-- source:
--   Yu, Chen, Lü, Kurths, Synchronization via pinning control on general complex networks, SIAM J. Control Optim. 51 (2013), p. 1399, Lemma 2.5

import Mathlib
import Definitions.Def_PinningSync_Strong_Setting

namespace PinningSync.Strong

theorem lemma_2_5 {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (hoff : ∀ i j, i ≠ j → 0 ≤ G i j) :
    IsIrred G ↔ IsStronglyConnected G := by sorry

end PinningSync.Strong
