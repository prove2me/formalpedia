-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeMaximalPlanarExtension__p2m_e8d3fd6d_990f_43df_873b_df1b4f477345_a2
-- name    : WilliamsonShmoys.edgeMaximalPlanarExtension__p2m_e8d3fd6d_990f_43df_873b_df1b4f477345_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:04:45.022794+00:00
-- url     : https://prove2.me/theorems/5e5b150a-02d6-4c7e-b48f-ee76aa630368
-- title:
--   Existence of an edge-maximal planar extension
-- statement:
--   Every planar graph on a finite fixed vertex type has a planar supergraph that is maximal under edge inclusion among planar graphs on that type. The proof route is to maximize edge count over the finite set of candidate edge sets. This handles empty or disconnected starting graphs without requiring extra hypotheses; the child’s remaining work is to formalize the finite maximization while preserving the drawing witness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edgeMaximalPlanarExtension__p2m_e8d3fd6d_990f_43df_873b_df1b4f477345_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      HasPlanarDrawingOn K ∧
      (letI : DecidableRel H.Adj := dH
       letI : DecidableRel K.Adj := dK
       H.edgeFinset ⊆ K.edgeFinset) ∧
      ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
        HasPlanarDrawingOn L →
        (letI : DecidableRel K.Adj := dK
         letI : DecidableRel L.Adj := dL
         K.edgeFinset ⊆ L.edgeFinset → L.edgeFinset ⊆ K.edgeFinset) := by sorry
