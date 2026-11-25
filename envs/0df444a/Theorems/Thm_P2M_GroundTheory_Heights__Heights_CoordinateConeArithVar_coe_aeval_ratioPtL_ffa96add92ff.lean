-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_coe_aeval_ratioPtL_ffa96add92ff
-- name    : P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_coe_aeval_ratioPtL_ffa96add92ff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:58.838429+00:00
-- url     : https://prove2.me/theorems/cb5cc882-07da-4a00-8d52-097de0854c24
-- title:
--   P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var coe aeval ratio Pt L ffa96add92ff: P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var coe aeval ratio Pt L ffa96add92ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var coe aeval ratio Pt L ffa96add92ff construction uses the P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var coe aeval ratio Pt L ffa96add92ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L241-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L241-L246

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_coe_aeval_ratioPtL_ffa96add92ff [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (f : MRing ι) :
    ((aeval (ratioPtL y c) f : ratioField y c) : Ω) = aeval (ratioPt y c) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CoordinateConeArithVar».«coe_aeval_ratioPtL» := P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_coe_aeval_ratioPtL_ffa96add92ff
