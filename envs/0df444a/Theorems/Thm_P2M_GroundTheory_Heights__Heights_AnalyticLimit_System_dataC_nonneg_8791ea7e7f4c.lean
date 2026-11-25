-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_dataC_nonneg_8791ea7e7f4c
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_dataC_nonneg_8791ea7e7f4c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:30:26.750277+00:00
-- url     : https://prove2.me/theorems/c36a2cb6-9d36-4bf9-b773-91b305986f75
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit System data C nonneg 8791ea7e7f4c: P2 M Ground Theory Heights  Heights Analytic Limit System data C nonneg 8791ea7e7f4c
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit System data C nonneg 8791ea7e7f4c construction uses the P2 M Ground Theory Heights  Heights Analytic Limit System data C nonneg 8791ea7e7f4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Telescoping.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Telescoping.lean#L65-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Telescoping
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)
noncomputable section
open GroundTheory.Heights₂.Heights.AnalyticLimit.System
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} {R : RegChartData A}
  (S : System R)

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_dataC_nonneg_8791ea7e7f4c {x : X} (hx : x ∈ R.Yo) : 0 ≤ R.C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«System».«dataC_nonneg» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_dataC_nonneg_8791ea7e7f4c
