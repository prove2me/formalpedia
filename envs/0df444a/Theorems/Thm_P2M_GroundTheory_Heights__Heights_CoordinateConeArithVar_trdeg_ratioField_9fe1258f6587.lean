-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_trdeg_ratioField_9fe1258f6587
-- name    : P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_trdeg_ratioField_9fe1258f6587
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:56:56.521272+00:00
-- url     : https://prove2.me/theorems/7c53e571-b537-4eea-a16b-3afd66d86c69
-- title:
--   P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var trdeg ratio Field 9fe1258f6587: P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var trdeg ratio Field 9fe1258f6587
-- statement:
--   The P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var trdeg ratio Field 9fe1258f6587 construction uses the P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var trdeg ratio Field 9fe1258f6587 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L261-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L261-L291

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

theorem P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_trdeg_ratioField_9fe1258f6587 [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : ℕ) (t : Fin d → Ω)
    (ht : AlgebraicIndependent ℚ t) (htL : ∀ i, t i ∈ ratioField y c)
    (halg : ∀ r ∈ coneRatios y c, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) r) :
    Algebra.trdeg ℤ (ratioField y c) = d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CoordinateConeArithVar».«trdeg_ratioField» := P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_trdeg_ratioField_9fe1258f6587
