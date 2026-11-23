-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen_of_isGen
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen_of_isGen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:47:12.052049+00:00
-- url     : https://prove2.me/theorems/1ebd0bf3-005d-45a1-8784-1ab4da0ca0e5
-- title:
--   DVR: pull Gen is Gen of is Gen
-- statement:
--   The DVR construction uses the pull Gen is Gen of is Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullUUnitsCompatGeneric.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullUUnitsCompatGeneric.lean#L59-L63

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen_of_isGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (h : Z ⟶ Y) : (LB.pullGen L φ ε t h).IsGen := by sorry
