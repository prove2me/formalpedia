-- Prove2me | Theorems.Thm_SimpleGraph_exists_maximal_supgraph_of_finite__p2m_2dea5b09_c429_4a5e_b3c1_b82fac24916e_a2
-- name    : SimpleGraph.exists_maximal_supgraph_of_finite__p2m_2dea5b09_c429_4a5e_b3c1_b82fac24916e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:47:26.407711+00:00
-- url     : https://prove2.me/theorems/288a21a7-124b-4604-83f4-05f43dd10c79
-- title:
--   Finite downward-closed graph properties have maximal extensions
-- statement:
--   On a finite vertex type, every graph satisfying a downward-closed graph property is contained in a graph maximal among those satisfying the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem SimpleGraph.exists_maximal_supgraph_of_finite__p2m_2dea5b09_c429_4a5e_b3c1_b82fac24916e_a2
    {V : Type} [Fintype V] (P : SimpleGraph V → Prop)
    (hdown : ∀ ⦃G H : SimpleGraph V⦄, H ≤ G → P G → P H)
    (K : SimpleGraph V) (hK : P K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ P L ∧
      ∀ M : SimpleGraph V, L ≤ M → P M → M ≤ L := by sorry
