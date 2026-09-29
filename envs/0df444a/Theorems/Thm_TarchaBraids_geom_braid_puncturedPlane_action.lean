-- Prove2me | Theorems.Thm_TarchaBraids_geom_braid_puncturedPlane_action
-- name    : TarchaBraids.geom_braid_puncturedPlane_action
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-21T22:06:07.485015+00:00
-- url     : https://prove2.me/theorems/82eb1917-1880-4285-b221-61b3fbfe0289
-- title:
--   Half-twists act on the standard loops by Artin's formulas
-- statement:
--   The braid group acts on the fundamental group of the punctured plane, and half-twists act on the standard loops by Artin's formulas.
--
--   Precisely, there is a homomorphism $\rho$ from the geometric braid group to the automorphism group of $\pi_1(E^2 - Q_n)$ such that the elementary half-twist $[\mathrm{ht}_i]$ acts on the standard loops by
--
--   $$x_i \longmapsto x_i\, x_{i+1}\, x_i^{-1}, \qquad x_{i+1} \longmapsto x_i, \qquad x_k \longmapsto x_k \ (k \neq i, i+1),$$
--
--   where $x_j$ denotes the class of the $j$-th standard loop and the indices $i$, $i+1$ are the strands the half-twist exchanges.
--
--   This is the geometric heart of Artin's theory, stated on named generators so that it can actually be used. It is the mapping-class description of the braid group: a loop of configurations is realised, by isotopy extension, as an ambient isotopy of the plane carrying the puncture set to itself, whose time-one map is a homeomorphism of $E^2 - Q_n$ fixing the base point. Such a homeomorphism induces an automorphism of the fundamental group; the assignment depends only on the homotopy class of the loop and is multiplicative, which is what makes $\rho$ a homomorphism. Evaluating it on an elementary half-twist gives the displayed formulas: dragging the $i$-th puncture around the $(i+1)$-st conjugates the $i$-th loop by itself and carries the $(i+1)$-st to the $i$-th.
--
--   The content not covered elsewhere is the isotopy extension step. Everything downstream of this statement is already discharged: together with a generator-matched identification $\pi_1(E^2 - Q_n) \cong F_n$, it yields `TarchaBraids.geom_braid_artin_action` by transport, which is one of the two halves of the injectivity direction of Artin's presentation theorem.
--
--   Note the statement is about the *geometric* braid group, $\pi_1$ of the unordered configuration space, not the abstract Artin braid group. The corresponding statement for the abstract group is `BraidsLinksMCG.artin_representation_wellDefined`, which is proved and is purely algebraic: one checks the braid relations hold among Artin's automorphisms. No such check is available here, because the source is a fundamental group rather than a presented group, and this is exactly why the topological input is needed.
-- source:
--   Birman, Braids, Links and Mapping Class Groups, Chapter 1, equation (1-14); Artin, Theory of braids, Ann. of Math. 48 (1947).

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

open BraidsLinksMCG

theorem geom_braid_puncturedPlane_action (n : ℕ) :
    ∃ rho : GeomBraidGroup n →* MulAut (PuncturedPlaneGroup n),
      ∀ i : Fin (n - 1), ∀ j : Fin n,
        rho (halfTwistBraid n i) (standardGen n j) =
          (if j = strandIdx i then
              standardGen n (strandIdx i) * standardGen n (strandIdxSucc i) *
                (standardGen n (strandIdx i))⁻¹
            else if j = strandIdxSucc i then standardGen n (strandIdx i)
            else standardGen n j) := by sorry

end TarchaBraids
