-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_relIndex_pi_const
-- name    : ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.relIndex_pi_const
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:48:06.025558+00:00
-- url     : https://prove2.me/theorems/d674177f-d253-4025-b08b-cb1d3db1778f
-- title:
--   Satake Vectors: rel Index pi const
-- statement:
--   The Satake Vectors construction uses the rel Index pi const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L139-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L139-L161

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsIntMultiple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]

theorem ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.relIndex_pi_const {M : Type*} [AddCommGroup M] (H L : AddSubgroup M) (k : ℕ) :
    (AddSubgroup.pi Set.univ fun _ : Fin k => H).relIndex (AddSubgroup.pi Set.univ fun _ : Fin k => L)
      = H.relIndex L ^ k := by sorry
