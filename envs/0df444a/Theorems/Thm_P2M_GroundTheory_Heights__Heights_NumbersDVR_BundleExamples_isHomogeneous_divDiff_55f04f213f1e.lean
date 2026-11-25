-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isHomogeneous_divDiff_55f04f213f1e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isHomogeneous_divDiff_55f04f213f1e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:20.421498+00:00
-- url     : https://prove2.me/theorems/85f58ef7-4f4b-4d00-845b-239187e11c17
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples is Homogeneous div Diff 55f04f213f1e: P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples is Homogeneous div Diff 55f04f213f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples is Homogeneous div Diff 55f04f213f1e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples is Homogeneous div Diff 55f04f213f1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L169-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L169-L199

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isHomogeneous_divDiff_55f04f213f1e {r : ℕ} (l : Fin r) {G : MvPolynomial (Fin r) ℤ} {d : ℕ}
    (hG : G.IsHomogeneous (d + 1)) : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G).IsHomogeneous d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BundleExamples».«isHomogeneous_divDiff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isHomogeneous_divDiff_55f04f213f1e
