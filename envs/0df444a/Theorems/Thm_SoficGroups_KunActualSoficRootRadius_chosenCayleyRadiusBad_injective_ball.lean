-- Prove2me | Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosenCayleyRadiusBad_injective_ball
-- name    : SoficGroups.KunActualSoficRootRadius.chosenCayleyRadiusBad_injective_ball
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/7ec29be6-a4c5-4c6c-91b6-7f75e9f9a27e
-- title:
--   SoficGroups.KunActualSoficRootRadius.chosenCayleyRadiusBad_injective_ball
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSoficRootRadius
open Filter Topology
open scoped BigOperators Pointwise

theorem SoficGroups.KunActualSoficRootRadius.chosenCayleyRadiusBad_injective_ball
    {G : Type*} [Group G] [DecidableEq G]
    (A : SoficGroups.SoficApproximation G)
    (S : Finset G) (w : G → List ↥S) (n r : ℕ)
    {x : Fin (A.model n).size}
    (hx : x ∉ chosenCayleyRadiusBad A S w n r) :
    Set.InjOn (fun g : G => (A.model n).action g x)
      (↑(S ^ r) : Set G) := by sorry
