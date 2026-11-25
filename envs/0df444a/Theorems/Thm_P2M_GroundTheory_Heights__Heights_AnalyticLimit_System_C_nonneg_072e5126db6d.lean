-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_C_nonneg_072e5126db6d
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_C_nonneg_072e5126db6d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:29:30.823884+00:00
-- url     : https://prove2.me/theorems/44edd288-4688-4fae-b5cc-05c830289818
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit System C nonneg 072e5126db6d: P2 M Ground Theory Heights  Heights Analytic Limit System C nonneg 072e5126db6d
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit System C nonneg 072e5126db6d construction uses the P2 M Ground Theory Heights  Heights Analytic Limit System C nonneg 072e5126db6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Telescoping.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Telescoping.lean#L60-L63

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_C_nonneg_072e5126db6d {t : ℝ} (ht : 0 < t) (h0 : S.ell₀ ≤ ell t) (h1 : 1 ≤ ell t) (x : X) : 0 ≤ S.C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«System».«C_nonneg» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_C_nonneg_072e5126db6d
