-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_exists_homog_of_mem_quotPart_0d5b906c3b31
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_exists_homog_of_mem_quotPart_0d5b906c3b31
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:28:29.840122+00:00
-- url     : https://prove2.me/theorems/f492c797-a74f-424f-bdc8-b89dc4f94861
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell Loc Eval exists homog of mem quot Part 0d5b906c3b31: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell Loc Eval exists homog of mem quot Part 0d5b906c3b31 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell Loc Eval exists homog of mem quot Part 0d5b906c3b31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsHomogOfMemQuotPartAlt.lean#L184-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsHomogOfMemQuotPartAlt.lean#L184-L207

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
variable {V : Ideal (MRingOver S ι)}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_exists_homog_of_mem_quotPart_0d5b906c3b31 {d : K → ℤ} {m : MRingOver S ι ⧸ V} (hm : m ∈ quotPart S V d) :
    ∃ g : MRingOver S ι, IsMultiHomog g (fun k => (d k).toNat) ∧ ((∀ k, 0 ≤ d k) ∨ g = 0) ∧
      Ideal.Quotient.mk V g = m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«CellLocEval».«exists_homog_of_mem_quotPart» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_exists_homog_of_mem_quotPart_0d5b906c3b31
