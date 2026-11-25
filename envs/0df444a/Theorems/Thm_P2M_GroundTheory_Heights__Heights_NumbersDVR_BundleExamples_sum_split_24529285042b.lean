-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_sum_split_24529285042b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_sum_split_24529285042b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:04.608647+00:00
-- url     : https://prove2.me/theorems/114db4ba-8ca7-48c8-bfdd-b4af2a5ff8fd
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples sum split 24529285042b: P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples sum split 24529285042b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples sum split 24529285042b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples sum split 24529285042b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L147-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L147-L167

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_sum_split_24529285042b {r : ℕ} (l : Fin r) (f : Fin r → ℕ) :
    ∑ j, f j = (∑ j ∈ Finset.univ.filter (fun j => j < l), f j) + f l +
      ∑ j ∈ Finset.univ.filter (fun j => l < j), f j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BundleExamples».«sum_split» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_sum_split_24529285042b
