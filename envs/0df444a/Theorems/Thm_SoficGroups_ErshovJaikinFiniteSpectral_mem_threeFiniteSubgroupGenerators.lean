-- Prove2me | Theorems.Thm_SoficGroups_ErshovJaikinFiniteSpectral_mem_threeFiniteSubgroupGenerators
-- name    : SoficGroups.ErshovJaikinFiniteSpectral.mem_threeFiniteSubgroupGenerators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/0de8d82d-51a8-41b1-8281-e231a3617d5f
-- title:
--   SoficGroups.ErshovJaikinFiniteSpectral.mem_threeFiniteSubgroupGenerators
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ErshovJaikinFiniteSpectral
open Filter Topology
universe u v

theorem SoficGroups.ErshovJaikinFiniteSpectral.mem_threeFiniteSubgroupGenerators
    {G : Type u} [Group G] (K : Fin 3 → Subgroup G)
    [∀ i, Fintype (K i)] (g : G) :
    g ∈ threeFiniteSubgroupGenerators K ↔ ∃ i : Fin 3, g ∈ K i := by sorry
