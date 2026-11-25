-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_proof_ca1c1cb4046c
-- name    : P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_proof_ca1c1cb4046c
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:58:09.02775+00:00
-- url     : https://prove2.me/theorems/d8f2a99d-d244-426d-ba2c-8e9d874b3d59
-- title:
--   P2 M Ground Theory Heights  Heights Pts Sheet Only Null proof ca1c1cb4046c: P2 M Ground Theory Heights  Heights Pts Sheet Only Null proof ca1c1cb4046c
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Sheet Only Null proof ca1c1cb4046c construction uses the P2 M Ground Theory Heights  Heights Pts Sheet Only Null proof ca1c1cb4046c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSheetOnlyNull.lean#L317-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSheetOnlyNull.lean#L317-L353

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StCriticalFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSheetOnlyNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_proof_03186e126e60
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_osgood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_scaleBlock_mem_zeroLocus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_differentiableAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj IsMultiHomogIdeal mcPts segre fibre IsSheet scaleBlock
  scaleBlock_mem_zeroLocus segre_differentiableAt osgood fibreFinite)
open GroundTheory.Heights₂.Heights.PtsSheetOnlyNull
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_proof_ca1c1cb4046c (hC : CriticalFibreInfinite.Statement) : PtsSheetOnlyNull.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsSheetOnlyNull».«proof» := P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_proof_ca1c1cb4046c
