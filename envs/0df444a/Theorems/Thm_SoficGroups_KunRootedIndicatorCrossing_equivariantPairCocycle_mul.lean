-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_equivariantPairCocycle_mul
-- name    : SoficGroups.KunRootedIndicatorCrossing.equivariantPairCocycle_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/c6591a3e-436a-414b-8d4b-2f37626806a9
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.equivariantPairCocycle_mul
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology

theorem SoficGroups.KunRootedIndicatorCrossing.equivariantPairCocycle_mul {G : Type u} [Group G]
    (K : Matrix (G × G) (G × G) ℂ)
    (R : EquivariantHilbertKernelRealization K)
    (hadd : ∀ g h j : G, ∀ q : G × G,
      K (g, h) q + K (h, j) q = K (g, j) q)
    (a g : G) :
    equivariantPairCocycle R (a * g) =
      equivariantPairCocycle R a +
        R.representation a (equivariantPairCocycle R g) := by sorry
