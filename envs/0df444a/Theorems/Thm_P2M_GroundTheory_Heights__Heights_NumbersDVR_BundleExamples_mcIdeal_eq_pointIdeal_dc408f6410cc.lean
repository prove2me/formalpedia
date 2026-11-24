-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_mcIdeal_eq_pointIdeal_dc408f6410cc
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_mcIdeal_eq_pointIdeal_dc408f6410cc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:13.017604+00:00
-- url     : https://prove2.me/theorems/998a81ee-e6c9-4192-84d7-5ffd4e529515
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples mc Ideal eq point Ideal dc408f6410cc: P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples mc Ideal eq point Ideal dc408f6410
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples mc Ideal eq point Ideal dc408f6410cc construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples mc Ideal eq point Ideal dc408f6410cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L24-L25

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_mcIdeal_eq_pointIdeal_dc408f6410cc (R : Type*) [CommRing R] {Ω : Type*} [Field Ω] [Algebra R Ω]
    (y : (Σ k, ι k) → Ω) : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal R y = pointIdeal R y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BundleExamples».«mcIdeal_eq_pointIdeal» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_mcIdeal_eq_pointIdeal_dc408f6410cc
