-- Prove2me | Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosenCayleyRadiusBad_rooted
-- name    : SoficGroups.KunActualSoficRootRadius.chosenCayleyRadiusBad_rooted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/757c0952-bbd8-411e-be79-5902ceb6c8ed
-- title:
--   SoficGroups.KunActualSoficRootRadius.chosenCayleyRadiusBad_rooted
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

theorem SoficGroups.KunActualSoficRootRadius.chosenCayleyRadiusBad_rooted
    {G : Type*} [Group G] [DecidableEq G]
    (A : SoficGroups.SoficApproximation G)
    (S : Finset G) (hone : 1 ∈ S)
    (w : G → List ↥S)
    (hw : ∀ g, ((w g).map fun i : ↥S => (i : G)).prod = g)
    (n r : ℕ) (a g : G)
    (hword : (w a).length + (w g).length +
      (w (a * g)).length ≤ r)
    {x : Fin (A.model n).size}
    (hx : x ∉ chosenCayleyRadiusBad A S w n r) :
    chosenWordEvaluation A (fun i : ↥S => (i : G)) w n (a * g) x =
      (chosenWordEvaluation A (fun i : ↥S => (i : G)) w n a *
        chosenWordEvaluation A (fun i : ↥S => (i : G)) w n g) x := by sorry
