-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_vEval_eq_85c4d0bed24d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_vEval_eq_85c4d0bed24d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:31:19.564454+00:00
-- url     : https://prove2.me/theorems/1e87c0ae-e6cb-46b1-a4a5-f51693a15a26
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples v Eval eq 85c4d0bed24d: P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples v Eval eq 85c4d0bed24d
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples v Eval eq 85c4d0bed24d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples v Eval eq 85c4d0bed24d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L97-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L97-L101

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_vEval_eq_85c4d0bed24d (J : Ideal (MRing ι (IsLocalRing.ResidueField O)) → ℤ)
    (Z : Ideal (MRing ι O) →₀ ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O J Z = cycEval (fun W => J (specialIdeal W)) ⇑Z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BundleExamples».«vEval_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_vEval_eq_85c4d0bed24d
