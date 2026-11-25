-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_joinForm_eq_ec92fe149fc0
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_joinForm_eq_ec92fe149fc0
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:54.936524+00:00
-- url     : https://prove2.me/theorems/d1fa8331-df58-427b-bcdf-ee48001dab9a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples join Form eq ec92fe149fc0: P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples join Form eq ec92fe149fc0
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples join Form eq ec92fe149fc0 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples join Form eq ec92fe149fc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L249-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L249-L250

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
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
variable [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_joinForm_eq_ec92fe149fc0 {R : Type*} [CommRing R] (f : MRing ι R) :
    joinForm (ι' := ι') f = rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι') f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BundleExamples».«joinForm_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_joinForm_eq_ec92fe149fc0
