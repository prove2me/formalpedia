-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RhGradFStatement_holds
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.RhGradFStatement_holds
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:12:54.268262+00:00
-- url     : https://prove2.me/theorems/8066fcde-ef3b-4cd9-8db2-9955f21c0ba6
-- title:
--   Up: Rh Grad FStatement holds
-- statement:
--   The Up construction uses the Rh Grad FStatement holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/RhGradFPf.lean#L176-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/RhGradFPf.lean#L176-L177

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradFPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradFPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.RhGradFStatement_holds {E : Type} [Field E] [NumberField E] [IsCMField E] :
    RhGradFStatement (E := E) := by sorry
