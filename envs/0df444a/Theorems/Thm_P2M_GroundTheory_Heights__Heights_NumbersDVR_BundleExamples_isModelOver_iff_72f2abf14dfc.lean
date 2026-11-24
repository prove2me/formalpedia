-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isModelOver_iff_72f2abf14dfc
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isModelOver_iff_72f2abf14dfc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:08.017214+00:00
-- url     : https://prove2.me/theorems/302567a1-b0bf-4851-9694-f9bdc2b902c0
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples is Model Over iff 72f2abf14dfc: P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples is Model Over iff 72f2abf14dfc
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples is Model Over iff 72f2abf14dfc construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples is Model Over iff 72f2abf14dfc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L43-L50

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
variable (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isModelOver_iff_72f2abf14dfc (P : Ideal (MRing ι O)) (d : ℕ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d ↔ Nonempty K ∧ IsModelOver P d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BundleExamples».«isModelOver_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isModelOver_iff_72f2abf14dfc
