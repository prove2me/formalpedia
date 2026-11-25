-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mConeMap_monomial_00b34a9717a6
-- name    : P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mConeMap_monomial_00b34a9717a6
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:32.223476+00:00
-- url     : https://prove2.me/theorems/6efbf181-8ea9-49bd-8817-87779213c04d
-- title:
--   P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var m Cone Map monomial 00b34a9717a6: P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var m Cone Map monomial 00b34a9717a6
-- statement:
--   The P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var m Cone Map monomial 00b34a9717a6 construction uses the P2 M Ground Theory Heights  Heights Coordinate Cone Arith Var m Cone Map monomial 00b34a9717a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L20-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean#L20-L32

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

theorem P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mConeMap_monomial_00b34a9717a6 (y : (Σ k, ι k) → Ω) (e : (Σ k, ι k) →₀ ℕ) (a : ℤ) :
    mConeMap y (monomial e a) =
      monomial (e.mapDomain Sigma.fst) ((a : Ω) * e.prod fun p n ↦ y p ^ n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CoordinateConeArithVar».«mConeMap_monomial» := P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mConeMap_monomial_00b34a9717a6
