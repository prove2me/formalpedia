-- Prove2me | Theorems.Thm_SoficGroups_CompletedPrescribedSpectralRadiusSchedule_fixedRadiusRootBad_rooted
-- name    : SoficGroups.CompletedPrescribedSpectralRadiusSchedule.fixedRadiusRootBad_rooted
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/0d0b446f-9efd-49fe-b886-85ee4bf3be81
-- title:
--   SoficGroups.CompletedPrescribedSpectralRadiusSchedule.fixedRadiusRootBad_rooted
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedPrescribedSpectralRadiusSchedule
open Filter Topology
open scoped Pointwise

theorem SoficGroups.CompletedPrescribedSpectralRadiusSchedule.fixedRadiusRootBad_rooted
    {G V : Type*} [Group G] [DecidableEq G]
    [Fintype V] [DecidableEq V]
    (S : Finset G) (hone : 1 ∈ S)
    (w : G → List ↥S)
    (hw : ∀ a : G,
      ((w a).map fun i : ↥S => (i : G)).prod = a)
    (φ : G → Equiv.Perm V) (r : ℕ)
    (a g : G)
    (hr : (w a).length + (w g).length +
      (w (a * g)).length ≤ r)
    (x : V) (hx : x ∉ fixedRadiusRootBad φ S r) :
    φ (a * g) x = (φ a * φ g) x := by sorry
