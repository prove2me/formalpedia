-- Prove2me | Theorems.Thm_PlanarQueue_Planar_rainbow_iff
-- name    : PlanarQueue.Planar.rainbow_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:24:30.728325+00:00
-- url     : https://prove2.me/theorems/42ea838f-4467-4e24-9b09-3139b14bc357
-- title:
--   Rainbow characterization of queue layouts
-- statement:
--   Fix a linear order of the vertices of a finite graph $G$. A **rainbow** is a set of edges that pairwise nest in this order. The order admits a $k$-queue layout exactly when every rainbow has at most $k$ edges:
--
--   $$
--   \text{the order admits a }k\text{-queue layout}
--   \quad\Longleftrightarrow\quad
--   |R|\le k\text{ for every rainbow }R\subseteq E(G).
--   $$
--
--   This characterization converts a queue assignment question into a bound on nested matchings. The paper cites it in its proof of Lemma 9.
--
--   **Formalization Note** The vertex order is represented by an injective map to the natural numbers. Rainbows contain only actual graph edges.
-- source:
--   Dujmović, Joret, Micek, Morin, Ueckerdt, Wood, Planar graphs have bounded queue-number, arXiv:1904.04791v5, p. 10, proof of Lemma 9, citing Heath–Rosenberg [69]

import Mathlib
import Definitions.Def_PlanarQueue_Planar_Setting

namespace PlanarQueue.Planar

/-- Heath–Rosenberg's rainbow characterization, quoted in the proof of Lemma 9. -/
theorem rainbow_iff {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) (ord : V → ℕ) (hord : Function.Injective ord) :
    OrderAdmits G k ord ↔
      ∀ R : Finset (Sym2 V), (R : Set (Sym2 V)) ⊆ G.edgeSet →
        (R : Set (Sym2 V)).Pairwise (Nested ord) → R.card ≤ k := by sorry

end PlanarQueue.Planar
