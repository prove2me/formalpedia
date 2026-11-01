-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeFinset_card_independent_of_decidableRel__p2m_17cdf377_ddf7_4ef9_90d4_89407a0a5949_a4
-- name    : WilliamsonShmoys.edgeFinset_card_independent_of_decidableRel__p2m_17cdf377_ddf7_4ef9_90d4_89407a0a5949_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:01:34.980927+00:00
-- url     : https://prove2.me/theorems/a656ee7f-22e0-405e-921c-81e5b8073e6a
-- title:
--   The edge count is independent of the adjacency decision procedure
-- statement:
--   The graph’s finite edge set, and hence its cardinality, does not depend on which decision procedure is used for adjacency. Prove this by extensionality of the finite edge sets and their membership characterization, then apply congruence of cardinality. This bridges the parent hypothesis’s `dK` edge count to the maximal-edge-count child’s classical-decider edge count, resolving the previous diagnostic’s instance mismatch. The claim holds for every finite vertex type, including graphs with no edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edgeFinset_card_independent_of_decidableRel__p2m_17cdf377_ddf7_4ef9_90d4_89407a0a5949_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (d₁ d₂ : DecidableRel G.Adj) :
    (letI : DecidableRel G.Adj := d₁; G.edgeFinset.card) =
      (letI : DecidableRel G.Adj := d₂; G.edgeFinset.card) := by sorry
