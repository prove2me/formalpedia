-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_tele_near_d4efcaad67bd
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_tele_near_d4efcaad67bd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:30:11.382636+00:00
-- url     : https://prove2.me/theorems/a7279a32-d395-44ee-a717-d123e2cb54c4
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit System tele near d4efcaad67bd: P2 M Ground Theory Heights  Heights Analytic Limit System tele near d4efcaad67bd
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit System tele near d4efcaad67bd construction uses the P2 M Ground Theory Heights  Heights Analytic Limit System tele near d4efcaad67bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Telescoping.lean#L70-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Telescoping.lean#L70-L94

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_tele_near_d4efcaad67bd {t t' : ℝ} (ht' : 0 < t') (htt : t' ≤ t) (h0 : S.ell₀ ≤ ell t)
    (he : Real.exp 1 ≤ ell t) {x : X} (hx : x ∈ R.Yo) (hr : R.r x ≤ ell t) :
    |S.ph t x - S.ph t' x| ≤ S.teleConst * (t ^ (1 / 3 : ℝ) + errE S.C t) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«System».«tele_near» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_tele_near_d4efcaad67bd
