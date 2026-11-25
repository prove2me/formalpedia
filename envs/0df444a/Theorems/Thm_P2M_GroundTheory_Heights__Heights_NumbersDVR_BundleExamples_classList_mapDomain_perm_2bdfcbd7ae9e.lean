-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_classList_mapDomain_perm_2bdfcbd7ae9e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_classList_mapDomain_perm_2bdfcbd7ae9e
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:44:40.367411+00:00
-- url     : https://prove2.me/theorems/b8b13e79-c25a-55e8-9eb4-d391127a9876
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples class List map Domain perm 2bdfcbd7ae9e: P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples class List map Domain perm 2bdf
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples class List map Domain perm 2bdfcbd7ae9e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples class List map Domain perm 2bdfcbd7ae9e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L119-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L119-L122

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_classList_mapDomain_perm_2bdfcbd7ae9e {σ τ : Type*} (e : σ → τ) (cls : τ → K → ℤ) (μ : σ →₀ ℕ) :
    (classList cls (μ.mapDomain e)).Perm (classList (cls ∘ e) μ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BundleExamples».«classList_mapDomain_perm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_classList_mapDomain_perm_2bdfcbd7ae9e
