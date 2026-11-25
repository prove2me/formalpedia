-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_exists_rep_9868982c704f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_exists_rep_9868982c704f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:09.071806+00:00
-- url     : https://prove2.me/theorems/239f969a-395c-4958-bab1-84107beea107
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell Loc Eval exists rep 9868982c704f: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell Loc Eval exist
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell Loc Eval exists rep 9868982c704f construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell Loc Eval exists rep 9868982c704f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsHomogOfMemQuotPartAlt.lean#L209-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsHomogOfMemQuotPartAlt.lean#L209-L259

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_exists_rep_9868982c704f {T : Submonoid (MRingOver S ι)} {γ : K → ℤ}
    {x : LocalizedModule T (MRingOver S ι ⧸ V)} (hx : x ∈ locPart ι (quotPart S V) T γ) :
    ∃ (g : MRingOver S ι) (t : T) (a : K → ℕ), IsMultiHomog (t : MRingOver S ι) a ∧
      IsMultiHomog g (fun k => (γ k + a k).toNat) ∧ ((∀ k, 0 ≤ γ k + a k) ∨ g = 0) ∧
      x = LocalizedModule.mk (Ideal.Quotient.mk V g) t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«CellLocEval».«exists_rep» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_exists_rep_9868982c704f
