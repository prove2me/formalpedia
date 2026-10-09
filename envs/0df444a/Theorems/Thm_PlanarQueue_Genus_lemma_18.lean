-- Prove2me | Theorems.Thm_PlanarQueue_Genus_lemma_18
-- name    : PlanarQueue.Genus.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:22:23.390975+00:00
-- url     : https://prove2.me/theorems/12111f24-c8da-414d-ae36-a4edc91d1f4c
-- title:
--   Lemma 18 — every BFS layering of a planar graph carries a 49-queue layout ordered layer by layer
-- statement:
--   Let $G$ be a finite planar graph and let $(V_0, V_1, \dots)$ be a BFS layering of $G$. Then there is a $49$-queue layout of $G$ whose vertex ordering is
--   $$\vec V_0,\ \vec V_1,\ \vec V_2,\ \dots,$$
--   where $\vec V_i$ is some ordering of $V_i$: every vertex of $V_i$ precedes every vertex of $V_j$ whenever $i < j$.
--
--   The layer-by-layer shape of the ordering is what makes the lemma usable for graphs on surfaces: in the proof of Theorem 2 the vertices of a small set $Z$ are inserted between the layers, and the $49$ queues of the planar part stay queues.
--
--   **Formalization Note** The layering is a layer function $L$ that is a BFS layering of $G$ (one root per component); the conclusion asks for an injective order $\mathrm{ord}$ admitting a $49$-queue layout with $L(v) < L(w) \Rightarrow \mathrm{ord}(v) < \mathrm{ord}(w)$. Planarity is the published `RobertsonSeymour1986.GM5.IsPlanar` (a crossing-free drawing in $\mathbb R^2$ by simple arcs).
-- source:
--   Dujmović, Joret, Micek, Morin, Ueckerdt, Wood, Planar graphs have bounded queue-number, arXiv:1904.04791v5, p. 18, Lemma 18

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar
import Definitions.Def_PlanarQueue_Genus_Setting

namespace PlanarQueue.Genus

/-- Lemma 18 (p. 18): for every BFS layering `L` of a planar graph `G` there is a 49-queue layout of
`G` whose vertex ordering lists the layers in order (`V⃗₀, V⃗₁, …`). -/
theorem lemma_18 (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : RobertsonSeymour1986.GM5.IsPlanar G) (L : V → ℕ) (hL : IsBFSLayering G L) :
    ∃ ord : V → ℕ, PlanarQueue.Planar.OrderAdmits G 49 ord ∧ ∀ v w : V, L v < L w → ord v < ord w := by sorry

end PlanarQueue.Genus
