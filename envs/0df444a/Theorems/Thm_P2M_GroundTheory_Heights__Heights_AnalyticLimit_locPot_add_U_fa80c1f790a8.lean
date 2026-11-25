-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_locPot_add_U_fa80c1f790a8
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_locPot_add_U_fa80c1f790a8
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:14:40.848557+00:00
-- url     : https://prove2.me/theorems/ca23f4e0-dc68-534f-8bea-a340e85cdb5f
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit loc Pot add U fa80c1f790a8: P2 M Ground Theory Heights  Heights Analytic Limit loc Pot add U fa80c1f790a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit loc Pot add U fa80c1f790a8 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit loc Pot add U fa80c1f790a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Objects.lean#L22-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Objects.lean#L22-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
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
open MeasureTheory Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot mInt MIntegrable)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ThGe ell errE)
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X]

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_locPot_add_U_fa80c1f790a8 (P Q : LocPot X) (x : X) : (P + Q).U x = P.U x ∩ Q.U x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«locPot_add_U» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_locPot_add_U_fa80c1f790a8
