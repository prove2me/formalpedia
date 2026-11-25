-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_ratio_mem_bfdbef1de55d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_ratio_mem_bfdbef1de55d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:10:00.024087+00:00
-- url     : https://prove2.me/theorems/541cfa62-628c-4891-bff7-9ff4ef542b06
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist ratio mem bfdbef1de55d: P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist ratio mem bfdbef1de55d
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist ratio mem bfdbef1de55d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist ratio mem bfdbef1de55d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwistedDualGensExist.lean#L218-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwistedDualGensExist.lean#L218-L234

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensExist
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
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
  {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_ratio_mem_bfdbef1de55d (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} (hc : segreVec y c ≠ 0)
    (k : K) (j : ι k) : y ⟨k, j⟩ / y ⟨k, c k⟩ ∈ chartRing O (segreVec y) c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«TwistedDualGensExist».«ratio_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_ratio_mem_bfdbef1de55d
