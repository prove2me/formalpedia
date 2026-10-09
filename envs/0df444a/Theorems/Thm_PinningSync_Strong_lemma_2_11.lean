-- Prove2me | Theorems.Thm_PinningSync_Strong_lemma_2_11
-- name    : PinningSync.Strong.lemma_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:24:20.022764+00:00
-- url     : https://prove2.me/theorems/72426836-9ae0-4496-80bc-ba85033f9759
-- title:
--   Lemma 2.11, p. 1401 — an irreducible G with zero row sums and Gᵢⱼ ≥ 0 (i ≠ j) has a positive x with Gᵀx = 0
-- statement:
--   Let $G$ be a coupling matrix: $G_{ij}\ge 0$ for $i\ne j$ and $\sum_{j=1}^N G_{ij}=0$ for every $i$. If $G$ is irreducible, then there is a positive vector $x$ (every $x_i>0$) with
--   $$
--   G^Tx=0 .
--   $$
--
--   The vector $x$ is a positive left null vector of $G$; it supplies the weights $\Xi=\operatorname{diag}(x)$ of Lemma 2.12 and Theorem 3.1. For an undirected or balanced network one may take $x=\mathbf 1_N$, but not for a general directed network.
--
--   **Formalization Note.** Irreducibility is Definition 2.4 (the permutation form). For $N=0$ the statement holds trivially.
-- source:
--   Yu, Chen, Lü, Kurths, Synchronization via pinning control on general complex networks, SIAM J. Control Optim. 51 (2013), p. 1401, Lemma 2.11

import Mathlib
import Definitions.Def_PinningSync_Strong_Setting

namespace PinningSync.Strong

open Matrix

theorem lemma_2_11 {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (hG : IsCouplingMatrix G)
    (hirr : IsIrred G) :
    ∃ x : Fin N → ℝ, (∀ i, 0 < x i) ∧ Gᵀ *ᵥ x = 0 := by sorry

end PinningSync.Strong
