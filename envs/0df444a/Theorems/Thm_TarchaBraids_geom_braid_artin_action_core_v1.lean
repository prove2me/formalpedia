-- Prove2me | Theorems.Thm_TarchaBraids_geom_braid_artin_action_core_v1
-- name    : TarchaBraids.geom_braid_artin_action_core_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-23T22:00:27.634906+00:00
-- url     : https://prove2.me/theorems/c9f9390f-92b3-4bf7-8269-25382c8e6027
-- title:
--   The geometric braid action on the free group is pinned on half-twists
-- statement:
--   This is the free-group form of the geometric Artin action. It asks for a homomorphism
--
--   $$
--   \rho\colon \pi_1(B_{0,n}E^2)\longrightarrow \operatorname{Aut}(F_n)
--   $$
--
--   such that the elementary geometric half-twist $\sigma_i$ acts on the free generators by Artin's formula
--
--   $$
--    x_i\longmapsto x_i x_{i+1}x_i^{-1},\qquad
--    x_{i+1}\longmapsto x_i,
--   $$
--
--   while all other generators are fixed. The geometric construction is obtained by extending a loop of configurations to an ambient isotopy of the plane and taking the induced action on the fundamental group of the punctured plane, followed by the generator-matched identification with $F_n$. The statement isolates this topological input before transport to the punctured-plane group.
-- source:
--   Birman, Braids, Links and Mapping Class Groups, Chapter 1, equation (1-14); Tarcha, Braid Theory and the Artin Presentation, the geometric form of the Artin representation.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

open BraidsLinksMCG

theorem geom_braid_artin_action_core_v1 (n : ℕ) :
    ∃ rho : GeomBraidGroup n →* MulAut (FreeGroup (Fin n)),
      ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
        rho (halfTwistBraid n i) w = artinEndo n i w := by sorry

end TarchaBraids
