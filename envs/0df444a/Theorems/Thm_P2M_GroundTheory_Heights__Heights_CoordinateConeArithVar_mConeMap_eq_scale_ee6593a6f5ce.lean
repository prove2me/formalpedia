-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mConeMap_eq_scale_ee6593a6f5ce
-- name    : P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mConeMap_eq_scale_ee6593a6f5ce
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:46.263429+00:00
-- url     : https://prove2.me/theorems/e33b118b-43ab-4eeb-b047-0fadbf0b3bee
-- title:
--   P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var m Cone Map eq scale ee6593a6f5ce: P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var m Cone Map eq scale ee6593a6f5ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var m Cone Map eq scale ee6593a6f5ce construction uses the P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var m Cone Map eq scale ee6593a6f5ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L126-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L126-L138

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

theorem P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mConeMap_eq_scale_ee6593a6f5ce (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (f : MRing ι) :
    mConeMap y f = scaleT (fun k ↦ y ⟨k, c k⟩) (mConeMap (ratioPt y c) f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CoordinateConeArithVar».«mConeMap_eq_scale» := P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mConeMap_eq_scale_ee6593a6f5ce
