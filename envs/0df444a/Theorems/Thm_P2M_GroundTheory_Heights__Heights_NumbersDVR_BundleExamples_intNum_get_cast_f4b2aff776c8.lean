-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_intNum_get_cast_f4b2aff776c8
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_intNum_get_cast_f4b2aff776c8
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:46.065141+00:00
-- url     : https://prove2.me/theorems/456904cf-515b-449b-88a3-c12aa99a6995
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples int Num get cast f4b2aff776c8: P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples int Num get cast f4b2aff776c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples int Num get cast f4b2aff776c8 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples int Num get cast f4b2aff776c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L114-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L114-L117

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_intNum_get_cast_f4b2aff776c8 (F : Type*) [Field F] (V : Ideal (MRing ι F)) (L : List (K → ℤ)) (n : ℕ)
    (h : L.length = n) : intNum F V (fun j => L.get (Fin.cast h.symm j)) = intNumL F V L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BundleExamples».«intNum_get_cast» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_intNum_get_cast_f4b2aff776c8
