-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_joinCoords_eq_eddac3903903
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_joinCoords_eq_eddac3903903
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:18.289742+00:00
-- url     : https://prove2.me/theorems/89d5d20b-25cf-413f-8ffc-883e7fd8f839
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples join Coords eq eddac3903903: P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples join Coords eq eddac3903903
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples join Coords eq eddac3903903 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples join Coords eq eddac3903903 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L244-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L244-L247

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_joinCoords_eq_eddac3903903 {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) :
    joinCoords y y' = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y y' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BundleExamples».«joinCoords_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_joinCoords_eq_eddac3903903
