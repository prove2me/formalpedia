-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_coe_mapDomain_fst_cfb4929795a1
-- name    : P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_coe_mapDomain_fst_cfb4929795a1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:56:34.206874+00:00
-- url     : https://prove2.me/theorems/ac75b6dc-94e5-5551-b967-f7258d2b275f
-- title:
--   P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var coe map Domain fst cfb4929795a1: P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var coe map Domain fst cfb4929795a1
-- statement:
--   The P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var coe map Domain fst cfb4929795a1 construction uses the P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var coe map Domain fst cfb4929795a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L36-L42

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

theorem P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_coe_mapDomain_fst_cfb4929795a1 [DecidableEq K] (e : (Σ k, ι k) →₀ ℕ) :
    ⇑(e.mapDomain Sigma.fst) = Finsupp.weight (NumbersDVR.blockWeight ι) e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CoordinateConeArithVar».«coe_mapDomain_fst» := P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_coe_mapDomain_fst_cfb4929795a1
