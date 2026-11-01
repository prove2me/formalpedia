-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_of_edgeFinset_subset__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a1__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a2
-- name    : WilliamsonShmoys.connected_of_edgeFinset_subset__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a1__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:18:50.804752+00:00
-- url     : https://prove2.me/theorems/0195948a-9fe1-4a57-8123-819a8504c992
-- title:
--   Connectivity under edge inclusion
-- statement:
--   Edge inclusion preserves connectivity on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_of_edgeFinset_subset__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a1__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    H.edgeFinset ⊆ K.edgeFinset → H.Connected → K.Connected := by sorry
