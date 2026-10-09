-- Prove2me | Theorems.Thm_PlanarQueue_Genus_extra_queues_4g
-- name    : PlanarQueue.Genus.extra_queues_4g
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:22:35.361768+00:00
-- url     : https://prove2.me/theorems/c287baaf-48b0-470f-b319-5c822a6b36a5
-- title:
--   §5, p. 23 — inserting Z layer by layer into a layered 49-queue layout of G − Z costs 4g new queues
-- statement:
--   Let $G$ be a finite graph with a layering $(V_0, V_1, \dots)$, let $g \ge 0$, and let $Z \subseteq V(G)$ be a set of vertices with
--   $$|V_j \cap Z| \le 2g \qquad \text{for every } j \ge 0.$$
--   Suppose that $G - Z$ has a $49$-queue layout whose vertex ordering lists $V_0 \setminus Z, V_1 \setminus Z, \dots$ in this order (each layer in some internal order). Then $G$ has a $(4g + 49)$-queue layout.
--
--   This is the last step of the paper's proof of Theorem 2: the vertices of $Z$ are placed in front of their layers, edges of $G - Z$ keep their queues, and the edges at the $i$-th vertex of $Z$ in odd layers, respectively even layers, form $2g + 2g$ new queues.
--
--   **Formalization Note** The layering is a layer function $L$, and $Z$ is a finite set of vertices. The layout of $G - Z$ is an injective order $\mathrm{ord}_0$ on the vertices outside $Z$ that admits a $49$-queue layout of the induced subgraph and satisfies $L(a) < L(b) \Rightarrow \mathrm{ord}_0(a) < \mathrm{ord}_0(b)$. The number $49$ is the page's; the argument itself works for any number $k$ of queues in place of $49$, giving $k + 4g$. The page's "Thus $|i - j| \geqslant 2$" means $|j - \ell| \ge 2$.
-- source:
--   Dujmović, Joret, Micek, Morin, Ueckerdt, Wood, Planar graphs have bounded queue-number, arXiv:1904.04791v5, §5, p. 23, proof of Theorem 2, "Hence this step introduces 4g new queues, and in total we have 4g + 49 queues"

import Mathlib
import Definitions.Def_PlanarQueue_Genus_Setting

namespace PlanarQueue.Genus

/-- The 4g-queue step of the proof of Theorem 2 (p. 23): if `G` has a layering `L`, a vertex set `Z`
with at most `2g` vertices in each layer, and `G − Z` has a 49-queue layout whose vertex order lists
the layers in order, then `G` has a `(4g + 49)`-queue layout. -/
theorem extra_queues_4g (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (L : V → ℕ) (hL : PlanarQueue.Planar.IsLayering G L) (g : ℕ) (Z : Finset V)
    (hZ : ∀ j : ℕ, (Z.filter (fun v => L v = j)).card ≤ 2 * g)
    (ord₀ : ↥((↑Z : Set V)ᶜ) → ℕ) (h₀ : PlanarQueue.Planar.OrderAdmits (G.induce (↑Z : Set V)ᶜ) 49 ord₀)
    (hmono : ∀ a b : ↥((↑Z : Set V)ᶜ), L a < L b → ord₀ a < ord₀ b) :
    PlanarQueue.Planar.HasQueueLayout G (4 * g + 49) := by sorry

end PlanarQueue.Genus
