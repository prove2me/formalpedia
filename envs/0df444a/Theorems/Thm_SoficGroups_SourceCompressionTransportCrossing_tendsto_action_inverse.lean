-- Prove2me | Theorems.Thm_SoficGroups_SourceCompressionTransportCrossing_tendsto_action_inverse
-- name    : SoficGroups.SourceCompressionTransportCrossing.tendsto_action_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/d7526af1-3f8d-445d-97e7-49f153ad48ca
-- title:
--   SoficGroups.SourceCompressionTransportCrossing.tendsto_action_inverse
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionTransportCrossing
open Filter Topology
open scoped BigOperators

theorem SoficGroups.SourceCompressionTransportCrossing.tendsto_action_inverse
    {G : Type*} [Group G] (A : SoficGroups.SoficApproximation G)
    (u : G) :
    Tendsto
      (fun n => SoficGroups.normalizedHamming
        (((A.model n).action u)⁻¹)
        ((A.model n).action (u⁻¹)))
      atTop (nhds 0) := by sorry
