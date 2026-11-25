-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointLineDegreeAlt_isMultiHomog_X_00c1ddf81f17
-- name    : P2M_GroundTheory_Heights__Heights_DualPointLineDegreeAlt_isMultiHomog_X_00c1ddf81f17
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:34.266733+00:00
-- url     : https://prove2.me/theorems/d1e9a530-7005-51e3-87e4-a79a01aa0c8e
-- title:
--   P2 M Ground Theory Heights  Heights Dual Point Line Degree Alt is Multi Homog X 00c1ddf81f17: P2 M Ground Theory Heights  Heights Dual Point Line Degree Alt is Multi Homog X 00c1ddf81f17
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Point Line Degree Alt is Multi Homog X 00c1ddf81f17 construction uses the P2 M Ground Theory Heights  Heights Dual Point Line Degree Alt is Multi Homog X 00c1ddf81f17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPointLineDegree.lean#L27-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPointLineDegree.lean#L27-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPointLineDegree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isMultiHomog_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial Matrix NumberField
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.DualPointLineDegreeAlt

theorem P2M_GroundTheory_Heights__Heights_DualPointLineDegreeAlt_isMultiHomog_X_00c1ddf81f17 {T : Type} [Fintype T] (t : T) :
    IsMultiHomog (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) (fun _ => 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualPointLineDegreeAlt».«isMultiHomog_X» := P2M_GroundTheory_Heights__Heights_DualPointLineDegreeAlt_isMultiHomog_X_00c1ddf81f17
