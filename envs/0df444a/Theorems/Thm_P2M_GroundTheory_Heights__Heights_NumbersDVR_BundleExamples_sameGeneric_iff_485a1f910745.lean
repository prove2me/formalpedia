-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_sameGeneric_iff_485a1f910745
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_sameGeneric_iff_485a1f910745
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:35:40.374858+00:00
-- url     : https://prove2.me/theorems/6471715e-2fcf-50cc-bbfe-d3d6f03b2437
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples same Generic iff 485a1f910745: P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples same Generic iff 485a1f910745
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples same Generic iff 485a1f910745 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples same Generic iff 485a1f910745 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L74-L80

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
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_sameGeneric_iff_485a1f910745 {ϖ : O} (hϖ : Irreducible ϖ) (x : (Σ k, ι k) → Ω)
    (E E' : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E' ↔ SameGenericFibre ϖ E E' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BundleExamples».«sameGeneric_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_sameGeneric_iff_485a1f910745
