-- Prove2me | Theorems.Thm_PlanarQueue_Planar_lemma_8
-- name    : PlanarQueue.Planar.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:24:29.352166+00:00
-- url     : https://prove2.me/theorems/e861b278-0745-439e-ac97-28151e437d2b
-- title:
--   Lemma 8 — queue layouts from layered partitions
-- statement:
--   Let $H$ have a $k$-queue layout. Suppose $G$ has an $H$-partition whose every part meets every layer of a fixed layering in at most $\ell$ vertices. Then $G$ has a queue layout ordered layer by layer, using at most
--
--   $$
--   3\ell k+\left\lfloor\frac{3\ell}{2}\right\rfloor
--   $$
--
--   queues. Every vertex in an earlier layer precedes every vertex in a later layer. This transfers a queue bound on the quotient pattern to the original graph.
--
--   **Formalization Note** The fixed layering is explicit, and the output order is monotone in it. Natural-number division by $2$ expresses the floor.
-- source:
--   Dujmović, Joret, Micek, Morin, Ueckerdt, Wood, Planar graphs have bounded queue-number, arXiv:1904.04791v5, p. 10, Lemma 8

import Mathlib
import Definitions.Def_PlanarQueue_Planar_Setting

namespace PlanarQueue.Planar

/-- Lemma 8: an H-partition of layered width ℓ lifts a k-queue layout of H. -/
theorem lemma_8 {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (k ℓ : ℕ)
    (hH : HasQueueLayout H k)
    (L : V → ℕ) (hL : IsLayering G L)
    (φ : V → W) (hφ : IsHPartition G H φ)
    (hw : ∀ x : W, ∀ i : ℕ,
      (Finset.univ.filter fun v : V => φ v = x ∧ L v = i).card ≤ ℓ) :
    ∃ ord : V → ℕ,
      OrderAdmits G (3 * ℓ * k + 3 * ℓ / 2) ord ∧
        ∀ v w : V, L v < L w → ord v < ord w := by sorry

end PlanarQueue.Planar
