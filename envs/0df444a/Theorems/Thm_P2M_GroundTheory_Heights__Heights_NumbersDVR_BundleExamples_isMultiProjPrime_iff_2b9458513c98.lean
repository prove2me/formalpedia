-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isMultiProjPrime_iff_2b9458513c98
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isMultiProjPrime_iff_2b9458513c98
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:48.143715+00:00
-- url     : https://prove2.me/theorems/17e48935-d2dd-43d5-a7c6-8d7d7dd9f9a2
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples is Multi Proj Prime iff 2b9458513c98: P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples is Multi Proj Prime iff 2b9458513c
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples is Multi Proj Prime iff 2b9458513c98 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples is Multi Proj Prime iff 2b9458513c98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L34-L41

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isMultiProjPrime_iff_2b9458513c98 (P : Ideal (MRing ι O)) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P ↔ IsMultiProjPrime P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BundleExamples».«isMultiProjPrime_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isMultiProjPrime_iff_2b9458513c98
