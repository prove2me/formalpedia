-- Prove2me | Theorems.Thm_SimpleGraph_exists_maximal_supergraph_of_downward_closed__p2m_407cedf5_8faa_4a1f_b011_cc5bdf645c63_a1
-- name    : SimpleGraph.exists_maximal_supergraph_of_downward_closed__p2m_407cedf5_8faa_4a1f_b011_cc5bdf645c63_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:41:59.561841+00:00
-- url     : https://prove2.me/theorems/d5bfcb69-9cee-4cff-a922-6b701f290b6c
-- title:
--   Finite maximal extension for a downward-closed graph property
-- statement:
--   On a finite vertex type, any downward-closed graph property true of G has a supergraph J that is maximal among graphs satisfying the property. The independent proof route is to maximize edge count over the finite family of property-satisfying supergraphs of G; any larger property-satisfying supergraph would contradict that maximum. This removes the finite selection and global maximality argument from the parent while preserving it as the core obligation of this reusable lemma.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem SimpleGraph.exists_maximal_supergraph_of_downward_closed__p2m_407cedf5_8faa_4a1f_b011_cc5bdf645c63_a1 {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (hdown : ∀ ⦃H K : SimpleGraph V⦄, H ≤ K → P K → P H) (G : SimpleGraph V) (hG : P G) : ∃ J : SimpleGraph V, G ≤ J ∧ P J ∧ ∀ K : SimpleGraph V, J ≤ K → P K → K = J := by sorry
