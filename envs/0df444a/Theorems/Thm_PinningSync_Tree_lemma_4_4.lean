-- Prove2me | Theorems.Thm_PinningSync_Tree_lemma_4_4
-- name    : PinningSync.Tree.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:19:29.772146+00:00
-- url     : https://prove2.me/theorems/ebf33653-5045-4f1b-972c-7bed9911caf7
-- title:
--   Lemma 4.4, p. 1406 — Π̃ⱼG̃ⱼ + G̃ⱼᵀΠ̃ⱼ < 0 on each diagonal block of a block lower-triangular Ḡ gives Δ > 0 with ΔΠ̃Ḡ + ḠᵀΠ̃Δ < 0
-- statement:
--   Let $\overline G\in\mathbb R^{N\times N}$ be block lower triangular with respect to an ordered partition of the indices into blocks $V_1,\dots,V_M$, i.e. $\overline G_{ab}=0$ whenever $a$ lies in an earlier block than $b$, as in (4.3). Write $\widetilde G_j$ for the diagonal block of $\overline G$ on $V_j$. Let $\pi\in\mathbb R^N$ be a positive vector and $\widetilde\Pi_j=\mathrm{diag}(\pi_a)_{a\in V_j}$. If
--   $$
--   \widetilde\Pi_j\widetilde G_j+\widetilde G_j^{\mathsf T}\widetilde\Pi_j<0\qquad\text{for every block } j, \tag{4.4}
--   $$
--   then there are positive constants $\Delta_1,\dots,\Delta_M$ such that, with $\Delta=\mathrm{diag}(\Delta_jI_{p_j})$ and $\widetilde\Pi=\mathrm{diag}(\widetilde\Pi_1,\dots,\widetilde\Pi_M)$,
--   $$
--   \Delta\widetilde\Pi\,\overline G+\overline G^{\mathsf T}\widetilde\Pi\Delta<0. \tag{4.5}
--   $$
--   Here $<0$ means negative definite.
--
--   The lemma lifts negative definiteness from the diagonal blocks to the whole block lower-triangular matrix by rescaling the blocks. It is what reduces the synchronization of the whole network to a condition on each strongly connected component in Theorem 4.5.
--
--   **Formalization Note** The indices are not permuted into block order: a map `blk : Fin N → Fin M` gives each index its block, the block order is the order of `Fin M`, and $\Delta\widetilde\Pi$ is the diagonal matrix with entries $\Delta_{\mathrm{blk}(a)}\pi_a$. This is the paper's matrix up to a simultaneous permutation of rows and columns, which preserves definiteness. Negative definiteness of $X$ is stated as positive definiteness of $-X$. As printed, $\overline G$ is an arbitrary block lower-triangular matrix and the $\widetilde\Pi_j$ arbitrary positive diagonal matrices.
-- source:
--   Yu, Chen, Lü, Kurths, Synchronization via pinning control on general complex networks, SIAM J. Control Optim. 51 (2013), p. 1406, Lemma 4.4, (4.3)–(4.5)

import Mathlib
import Definitions.Def_PinningSync_Tree_Setting

open Matrix Kronecker Filter Topology

namespace PinningSync.Tree

theorem lemma_4_4 {N M : ℕ} (blk : Fin N → Fin M) (Gbar : Matrix (Fin N) (Fin N) ℝ)
    (hGbar : ∀ i j, blk i < blk j → Gbar i j = 0) (π : Fin N → ℝ) (hπ : ∀ i, 0 < π i)
    (h44 : ∀ j : Fin M,
      (-(diagonal (fun a : Blk blk j => π a.val)
            * Gbar.submatrix (Subtype.val : Blk blk j → Fin N) Subtype.val
          + (Gbar.submatrix (Subtype.val : Blk blk j → Fin N) Subtype.val)ᵀ
            * diagonal (fun a : Blk blk j => π a.val))).PosDef) :
    ∃ Δ : Fin M → ℝ, (∀ j, 0 < Δ j) ∧
      (-(diagonal (fun i => Δ (blk i) * π i) * Gbar
          + Gbarᵀ * diagonal (fun i => Δ (blk i) * π i))).PosDef := by sorry

end PinningSync.Tree
