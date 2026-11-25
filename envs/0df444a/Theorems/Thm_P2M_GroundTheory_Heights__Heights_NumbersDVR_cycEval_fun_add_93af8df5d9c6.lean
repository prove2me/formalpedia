-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_fun_add_93af8df5d9c6
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_fun_add_93af8df5d9c6
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:09:37.399823+00:00
-- url     : https://prove2.me/theorems/b21d1a68-107a-4fed-a965-6ca095a3ccd1
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval fun add 93af8df5d9c6: P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval fun add 93af8df5d9c6
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval fun add 93af8df5d9c6 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval fun add 93af8df5d9c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L221-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairCocycle.lean#L221-L226

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_fun_add_93af8df5d9c6 {n₁ n₂ Z : Ideal (MRing ι R) → ℤ} (hZ : (Function.support Z).Finite) :
    cycEval (fun W => n₁ W + n₂ W) Z = cycEval n₁ Z + cycEval n₂ Z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«cycEval_fun_add» := P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_fun_add_93af8df5d9c6
