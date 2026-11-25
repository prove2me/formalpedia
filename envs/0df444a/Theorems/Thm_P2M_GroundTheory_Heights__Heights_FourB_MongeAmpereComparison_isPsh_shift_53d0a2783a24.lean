-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_isPsh_shift_53d0a2783a24
-- name    : P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_isPsh_shift_53d0a2783a24
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:36:01.729846+00:00
-- url     : https://prove2.me/theorems/9e9a4eea-2365-4063-92ee-bfd7ae8129cb
-- title:
--   P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison is Psh shift 53d0a2783a24: P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison is Psh shift 53d0a2783a24
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison is Psh shift 53d0a2783a24 construction uses the P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison is Psh shift 53d0a2783a24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereComparison.lean#L83-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereComparison.lean#L83-L141

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PMongeAmpereComparison
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison

theorem P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_isPsh_shift_53d0a2783a24 {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : LocPot X) (a b : X → ℝ) (k : ℝ) (hP : IsPotential A P) (ha : A.Smooth a)
    (hb : A.Smooth b) (hPa : IsPsh A (P + LocPot.ofFun a)) (hPb : IsPsh A (P + LocPot.ofFun b)) :
    IsPsh A ((P + LocPot.ofFun a) + LocPot.ofFun (fun x => cutoff (b x - a x + k))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«MongeAmpereComparison».«isPsh_shift» := P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_isPsh_shift_53d0a2783a24
