-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosDens_isSemiPosHerm_tensor_ad9d0c0ccfe9
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosDens_isSemiPosHerm_tensor_ad9d0c0ccfe9
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:22:56.948894+00:00
-- url     : https://prove2.me/theorems/e9746a45-3b39-5b55-915b-895dcc6577f8
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Dens is Semi Pos Herm tensor ad9d0c0ccfe9: P2 M Ground Theory Heights  Heights Pts Pos Dens is Semi Pos Herm tensor ad9d0c0ccfe9
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Dens is Semi Pos Herm tensor ad9d0c0ccfe9 construction uses the P2 M Ground Theory Heights  Heights Pts Pos Dens is Semi Pos Herm tensor ad9d0c0ccfe9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PtsPosDensMeasurable.lean#L75-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PtsPosDensMeasurable.lean#L75-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosDensIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsSumMeasurableA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsPosDensMeasurable
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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian
open GroundTheory.Heights₂.Heights.PtsPosDens
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_PtsPosDens_isSemiPosHerm_tensor_ad9d0c0ccfe9 {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (hAp : Inter.IsSemiPosHerm A) (hBp : Inter.IsSemiPosHerm B) : Inter.IsSemiPosHerm (A.tensor B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosDens».«isSemiPosHerm_tensor» := P2M_GroundTheory_Heights__Heights_PtsPosDens_isSemiPosHerm_tensor_ad9d0c0ccfe9
