-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_lincomb___d6eca3b5a7b8
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_lincomb___d6eca3b5a7b8
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:24:33.393618+00:00
-- url     : https://prove2.me/theorems/14f3e58a-bb45-52b6-ab5e-749e8acee344
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit lincomb   d6eca3b5a7b8: P2 M Ground Theory Heights  Heights Analytic Limit lincomb   d6eca3b5a7b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit lincomb   d6eca3b5a7b8 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit lincomb   d6eca3b5a7b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Objects.lean#L122-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Objects.lean#L122-L128

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_lincomb___d6eca3b5a7b8 (m : ℕ) (c : Fin m → ℝ) (P : Fin m → LocPot X) (x y : X) :
    (lincomb m c P).φ x y = ∑ i, c i * (P i).φ x y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«lincomb_φ» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_lincomb___d6eca3b5a7b8
