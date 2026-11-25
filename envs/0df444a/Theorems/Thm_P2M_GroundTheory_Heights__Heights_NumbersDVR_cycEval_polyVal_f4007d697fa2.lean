-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_polyVal_f4007d697fa2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_polyVal_f4007d697fa2
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:10:16.387425+00:00
-- url     : https://prove2.me/theorems/8d18b733-e7de-42c9-b38d-4a537bb8a8fa
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval poly Val f4007d697fa2: P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval poly Val f4007d697fa2
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval poly Val f4007d697fa2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval poly Val f4007d697fa2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L243-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L243-L251

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_polyVal_f4007d697fa2 {σ : Type*} {Z : Ideal (MRing ι R) → ℤ} (hZ : (Function.support Z).Finite)
    (F : Ideal (MRing ι R) → List (K → ℤ) → ℤ) (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ) :
    cycEval (fun W => polyVal (F W) cls H) Z = polyVal (fun l => cycEval (fun W => F W l) Z) cls H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«cycEval_polyVal» := P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_polyVal_f4007d697fa2
