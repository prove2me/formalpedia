-- Prove2me | Theorems.Thm_PlanarQueue_Planar_lemma_9
-- name    : PlanarQueue.Planar.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:24:20.389678+00:00
-- url     : https://prove2.me/theorems/d66da7de-f068-433b-95a4-18225b0b7296
-- title:
--   Lemma 9 — queue layout of a blowup
-- statement:
--   Let $H$ have a one-queue layout. Replace each vertex $x$ of $H$ by a block $B_x$ of at most $\ell$ vertices, and replace every edge $xy$ of $H$ by all edges between $B_x$ and $B_y$. Within each block choose any vertex order, and arrange the blocks in the order of $H$. The resulting graph $G$ admits an $\ell$-queue layout in that order:
--
--   $$
--   \operatorname{qn}_{\mathrm{block\ order}}(G)\le\ell.
--   $$
--
--   This is the blowup step used for each class of edges in Lemma 8.
--
--   **Formalization Note** The block map may have empty fibers. The adjacency equivalence asserts exactly the complete blowup, including the absence of edges within a block.
-- source:
--   Dujmović, Joret, Micek, Morin, Ueckerdt, Wood, Planar graphs have bounded queue-number, arXiv:1904.04791v5, p. 10, Lemma 9

import Mathlib
import Definitions.Def_PlanarQueue_Planar_Setting

namespace PlanarQueue.Planar

/-- Lemma 9: replacing each vertex of a one-queue graph by a block of at most ℓ vertices. -/
theorem lemma_9 {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (G : SimpleGraph V) (ℓ : ℕ)
    (ordH : W → ℕ) (hH : OrderAdmits H 1 ordH)
    (β : V → W) (hβ : ∀ x : W, (Finset.univ.filter fun v : V => β v = x).card ≤ ℓ)
    (hG : ∀ a b : V, G.Adj a b ↔ H.Adj (β a) (β b))
    (ordG : V → ℕ) (hordG : Function.Injective ordG)
    (hblocks : ∀ a b : V, ordH (β a) < ordH (β b) → ordG a < ordG b) :
    OrderAdmits G ℓ ordG := by sorry

end PlanarQueue.Planar
