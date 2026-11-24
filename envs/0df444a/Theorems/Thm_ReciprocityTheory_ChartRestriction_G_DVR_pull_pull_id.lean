-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pull_pull_id
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.pull_pull_id
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:12.733122+00:00
-- url     : https://prove2.me/theorems/7529f493-dfec-4834-9f00-18f6c9131ddf
-- title:
--   DVR: pull pull id
-- statement:
--   The DVR construction uses the pull pull id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullUUnitsCompatGeneric.lean#L110-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullUUnitsCompatGeneric.lean#L110-L115

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.pull_pull_id (z : Z ⟶ Y) (p : Y ⟶ Z) (hzp : z ≫ p = 𝟙 Z) {W : Y.Opens} {V : Z.Opens}
    (hW : W ≤ p ⁻¹ᵁ ⊤) (hV : V ≤ z ⁻¹ᵁ W) (c : Γ(Z, ⊤)ˣ) :
    res hV (pullU z W (res hW (pullU p ⊤ c))) = res (le_top : V ≤ ⊤) c := by sorry
