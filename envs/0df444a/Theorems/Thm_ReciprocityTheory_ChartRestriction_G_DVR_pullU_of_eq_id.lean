-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullU_of_eq_id
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.pullU_of_eq_id
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:11:32.064918+00:00
-- url     : https://prove2.me/theorems/27491b08-83fc-5d02-9a65-772fb40fe777
-- title:
--   DVR: pull U of eq id
-- statement:
--   The DVR construction uses the pull U of eq id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullUUnitsCompatGeneric.lean#L77-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullUUnitsCompatGeneric.lean#L77-L81

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.pullU_of_eq_id (f : Z ⟶ Z) (hf : f = 𝟙 Z) (U V : Z.Opens) (hV : V ≤ f ⁻¹ᵁ U) (hV' : V ≤ U)
    (c : Γ(Z, U)ˣ) : res hV (pullU f U c) = res hV' c := by sorry
