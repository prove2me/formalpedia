-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_ratCyc_eq_f84cd3040ff4
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_ratCyc_eq_f84cd3040ff4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:03.73817+00:00
-- url     : https://prove2.me/theorems/06bf5935-9c72-48b2-85e6-09a141b8a299
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples rat Cyc eq f84cd3040ff4: P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples rat Cyc eq f84cd3040ff4
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples rat Cyc eq f84cd3040ff4 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples rat Cyc eq f84cd3040ff4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L89-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L89-L92

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
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_ratCyc_eq_f84cd3040ff4 (P : Ideal (MRing ι O)) (f g : MRing ι O) :
    ⇑(IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O P f g) = ratDiv P f g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BundleExamples».«ratCyc_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_ratCyc_eq_f84cd3040ff4
