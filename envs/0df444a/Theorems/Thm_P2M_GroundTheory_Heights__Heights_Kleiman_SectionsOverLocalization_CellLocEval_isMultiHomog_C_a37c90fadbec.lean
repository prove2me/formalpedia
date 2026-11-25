-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_isMultiHomog_C_a37c90fadbec
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_isMultiHomog_C_a37c90fadbec
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:28:09.503804+00:00
-- url     : https://prove2.me/theorems/0340d235-7130-4717-a776-a6bb4504a135
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell Loc Eval is Multi Homog C a37c90fadbec: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell Loc Eval
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell Loc Eval is Multi Homog C a37c90fadbec construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell Loc Eval is Multi Homog C a37c90fadbec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsHomogOfMemQuotPartAlt.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsHomogOfMemQuotPartAlt.lean#L25-L29

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_isMultiHomog_C_a37c90fadbec (r : S) : IsMultiHomog (C r : MRingOver S ι) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«CellLocEval».«isMultiHomog_C» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_isMultiHomog_C_a37c90fadbec
