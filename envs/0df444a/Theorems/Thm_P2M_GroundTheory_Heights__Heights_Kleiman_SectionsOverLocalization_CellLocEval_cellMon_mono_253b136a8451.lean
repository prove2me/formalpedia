-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_cellMon_mono_253b136a8451
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_cellMon_mono_253b136a8451
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:02.095637+00:00
-- url     : https://prove2.me/theorems/48c9468b-9a9f-47a4-b690-286f38b152d8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell Loc Eval cell Mon mono 253b136a8451: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell Loc Eval ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell Loc Eval cell Mon mono 253b136a8451 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell Loc Eval cell Mon mono 253b136a8451 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsHomogOfMemQuotPartAlt.lean#L326-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsHomogOfMemQuotPartAlt.lean#L326-L329

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsHomogOfMemQuotPartAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cellRes faceSign cechD locPart cechCc mIdealOver mConeMapOver
  quotPart)
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_cellMon_mono_253b136a8451 {J I : ∀ k, Finset (ι k)} (h : ∀ k, J k ⊆ I k) : cellMon S J ≤ cellMon S I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«CellLocEval».«cellMon_mono» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_cellMon_mono_253b136a8451
