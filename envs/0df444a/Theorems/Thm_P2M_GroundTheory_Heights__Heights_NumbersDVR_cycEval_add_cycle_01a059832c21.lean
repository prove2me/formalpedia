-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_add_cycle_01a059832c21
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_add_cycle_01a059832c21
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:19.136287+00:00
-- url     : https://prove2.me/theorems/cc99ce17-0d3b-4f95-9797-a44ee4a8cfc3
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval add cycle 01a059832c21: P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval add cycle 01a059832c21
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval add cycle 01a059832c21 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval add cycle 01a059832c21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L206-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L206-L212

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
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_add_cycle_01a059832c21 {n Z₁ Z₂ : Ideal (MRing ι R) → ℤ} (h₁ : (Function.support Z₁).Finite)
    (h₂ : (Function.support Z₂).Finite) :
    cycEval n (Z₁ + Z₂) = cycEval n Z₁ + cycEval n Z₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«cycEval_add_cycle» := P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_add_cycle_01a059832c21
