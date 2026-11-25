-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_rep_of_mem_71352e8bebca
-- name    : P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_rep_of_mem_71352e8bebca
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:45.771376+00:00
-- url     : https://prove2.me/theorems/8a89d861-067a-56e3-9214-1d0b78330bb4
-- title:
--   P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var rep of mem 71352e8bebca: P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var rep of mem 71352e8bebca
-- statement:
--   The P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var rep of mem 71352e8bebca construction uses the P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var rep of mem 71352e8bebca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L182-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L182-L237

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
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_rep_of_mem_71352e8bebca [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {x : Ω} (hx : x ∈ ratioField y c) :
    ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧
      aeval (ratioPt y c) h ≠ 0 ∧ aeval (ratioPt y c) g = x * aeval (ratioPt y c) h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CoordinateConeArithVar».«rep_of_mem» := P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_rep_of_mem_71352e8bebca
