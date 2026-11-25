-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_monoList_eq_277864d5c7d3
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_monoList_eq_277864d5c7d3
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:55.487004+00:00
-- url     : https://prove2.me/theorems/f54ffb24-c8bd-4541-99fd-0159d6d2ecbf
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples mono List eq 277864d5c7d3: P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples mono List eq 277864d5c7d3
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples mono List eq 277864d5c7d3 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples mono List eq 277864d5c7d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L109-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L109-L112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomogIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
set_option linter.unusedSectionVars false
universe u
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_monoList_eq_277864d5c7d3 {r : ℕ} {A : Type*} (deg : Fin r → A) (μ : Fin r →₀ ℕ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg μ = (IndefiniteRowSideFullHecke.NumbersDVR.monoList μ).map deg := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BundleExamples».«monoList_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_monoList_eq_277864d5c7d3
