-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_tele_far_e081df8bf3a3
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_tele_far_e081df8bf3a3
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:29:27.566836+00:00
-- url     : https://prove2.me/theorems/5782f90c-3e77-589f-9bdf-8ac2f6aac5f9
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit System tele far e081df8bf3a3: P2 M Ground Theory Heights  Heights Analytic Limit System tele far e081df8bf3a3
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit System tele far e081df8bf3a3 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit System tele far e081df8bf3a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Telescoping.lean#L96-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Telescoping.lean#L96-L121

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_tele_far_e081df8bf3a3 {t t' : ℝ} (ht' : 0 < t') (htt : t' ≤ t) (h0 : S.ell₀ ≤ ell t)
    (he : Real.exp 1 ≤ ell t) {x : X} (hx : x ∈ R.Yo) (hr : ell t < R.r x) :
    |S.ph t x - S.ph t' x| ≤ S.teleConst * Real.log (R.r x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«System».«tele_far» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_tele_far_e081df8bf3a3
