-- Prove2me | Theorems.Thm_SoficGroups_LocalMultiplicativeOn_map_inv_of_mem
-- name    : SoficGroups.LocalMultiplicativeOn.map_inv_of_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/719071c3-aeb6-4bd3-aa52-6f7e55581246
-- title:
--   SoficGroups.LocalMultiplicativeOn.map_inv_of_mem
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.LocalMultiplicativeOn
variable {G : Type u} {H : Type v} [Group G] [Group H]

theorem SoficGroups.LocalMultiplicativeOn.map_inv_of_mem {s : Finset G} {f : G → H}
    (h : LocalMultiplicativeOn s f) {x : G} (hx : x ∈ s) (hi : x⁻¹ ∈ s) :
    f x⁻¹ = (f x)⁻¹ := by sorry
