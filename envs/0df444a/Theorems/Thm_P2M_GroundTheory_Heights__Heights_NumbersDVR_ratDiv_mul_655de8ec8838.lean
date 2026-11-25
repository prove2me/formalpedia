-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ratDiv_mul_655de8ec8838
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ratDiv_mul_655de8ec8838
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:22.737805+00:00
-- url     : https://prove2.me/theorems/15d11cd8-e229-47cf-937f-40fc5a23b239
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR rat Div mul 655de8ec8838: P2 M Ground Theory Heights  Heights Numbers DVR rat Div mul 655de8ec8838
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR rat Div mul 655de8ec8838 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR rat Div mul 655de8ec8838 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L410-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L410-L417

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialQuotDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorsCommute
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairCocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
universe u
variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [Fintype K] [∀ k, Fintype (ι k)]
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ratDiv_mul_655de8ec8838 {P : Ideal (MRing ι O)} [P.IsPrime] {f g f' g' : MRing ι O} (hf : f ∉ P)
    (hg : g ∉ P) (hf' : f' ∉ P) (hg' : g' ∉ P) :
    ratDiv P (f * f') (g * g') = ratDiv P f g + ratDiv P f' g' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ratDiv_mul» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ratDiv_mul_655de8ec8838
