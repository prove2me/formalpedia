-- Prove2me | Theorems.Thm_SoficGroups_ExceptionalRankOffset_rankDropCount_goodSubtype_eq
-- name    : SoficGroups.ExceptionalRankOffset.rankDropCount_goodSubtype_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/a83bc387-346e-4c78-a85a-6a00aa414dc7
-- title:
--   SoficGroups.ExceptionalRankOffset.rankDropCount_goodSubtype_eq
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
open SoficGroups.ExceptionalRankOffset
open Filter Topology
open scoped BigOperators

theorem SoficGroups.ExceptionalRankOffset.rankDropCount_goodSubtype_eq
    {ι : Type*}
    (G : Finset ι) (u v : ι → ℝ) (H r : ℝ) :
    SoficGroups.rankDropCount
        (fun i : {i // i ∈ G} => u i.1)
        (fun i : {i // i ∈ G} => v i.1) H r =
      ∑ i ∈ G,
        if ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋ then (1 : ℝ) else 0 := by sorry
