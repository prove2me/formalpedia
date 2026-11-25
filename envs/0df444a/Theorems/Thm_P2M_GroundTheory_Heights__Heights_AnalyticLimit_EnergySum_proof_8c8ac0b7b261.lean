-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_EnergySum_proof_8c8ac0b7b261
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_EnergySum_proof_8c8ac0b7b261
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:50:15.745706+00:00
-- url     : https://prove2.me/theorems/333749ac-e33a-5cc6-8f3d-5332c21920d7
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit Energy Sum proof 8c8ac0b7b261: P2 M Ground Theory Heights  Heights Analytic Limit Energy Sum proof 8c8ac0b7b261
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit Energy Sum proof 8c8ac0b7b261 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit Energy Sum proof 8c8ac0b7b261 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/EnergySum.lean#L149-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/EnergySum.lean#L149-L154

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProjectiveLinePartitionContinuousCoe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_EnergySum
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
open MeasureTheory
open scoped ContDiff ComplexOrder
open ReciprocityTheory.AnForm (hessC maDens mdisc levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt ChartPartition locDens integralWith)
noncomputable section
variable {D : ℕ}
variable {X : Type*} [TopologicalSpace X]

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_EnergySum_proof_8c8ac0b7b261 : EnergySum.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«EnergySum».«proof» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_EnergySum_proof_8c8ac0b7b261
