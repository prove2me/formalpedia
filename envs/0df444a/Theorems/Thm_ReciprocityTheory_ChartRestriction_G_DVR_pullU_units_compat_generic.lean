-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullU_units_compat_generic
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.pullU_units_compat_generic
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:12:10.238446+00:00
-- url     : https://prove2.me/theorems/ef9df956-674b-5a6a-8095-af9e3b98ec06
-- title:
--   DVR: pull U units compat generic
-- statement:
--   The DVR construction uses the pull U units compat generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullUUnitsCompatGeneric.lean#L38-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullUUnitsCompatGeneric.lean#L38-L57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem ReciprocityTheory.ChartRestriction.G.DVR.pullU_units_compat_generic (h : Z ⟶ Y) {Ui Uj : Y.Opens} {Wi Wj : Z.Opens} (hi : Wi ≤ h ⁻¹ᵁ Ui)
    (hj : Wj ≤ h ⁻¹ᵁ Uj) (ti : Γ(Y, Ui)ˣ) (tj : Γ(Y, Uj)ˣ) (g : Γ(Y, Ui ⊓ Uj)ˣ)
    (hc : res (inf_le_left : Ui ⊓ Uj ≤ Ui) ti = g * res (inf_le_right : Ui ⊓ Uj ≤ Uj) tj)
    (g' : Γ(Z, Wi ⊓ Wj)ˣ)
    (hg' : g' = res (le_inf (inf_le_left.trans hi) (inf_le_right.trans hj) : Wi ⊓ Wj ≤ h ⁻¹ᵁ (Ui ⊓ Uj))
      (pullU h _ g)) :
    res (inf_le_left : Wi ⊓ Wj ≤ Wi) (res hi (pullU h Ui ti)) =
      g' * res (inf_le_right : Wi ⊓ Wj ≤ Wj) (res hj (pullU h Uj tj)) := by sorry
