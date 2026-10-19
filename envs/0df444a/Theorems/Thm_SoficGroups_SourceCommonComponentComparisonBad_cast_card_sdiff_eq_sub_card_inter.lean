-- Prove2me | Theorems.Thm_SoficGroups_SourceCommonComponentComparisonBad_cast_card_sdiff_eq_sub_card_inter
-- name    : SoficGroups.SourceCommonComponentComparisonBad.cast_card_sdiff_eq_sub_card_inter
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/25bf5cdf-65b3-481f-afdd-643c335a21eb
-- title:
--   SoficGroups.SourceCommonComponentComparisonBad.cast_card_sdiff_eq_sub_card_inter
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCommonComponentComparisonBad
open Filter Topology
open scoped BigOperators

theorem SoficGroups.SourceCommonComponentComparisonBad.cast_card_sdiff_eq_sub_card_inter
    {V : Type*} [DecidableEq V] (C D : Finset V) :
    ((C \ D).card : ℝ) =
      (C.card : ℝ) - ((C ∩ D).card : ℝ) := by sorry
