-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfB_Ag_cont
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.Ag_cont
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:49:51.316462+00:00
-- url     : https://prove2.me/theorems/a4182130-1690-5b7d-9b1d-2aad8701f973
-- title:
--   Mode Half B: Ag cont
-- statement:
--   The Mode Half B construction uses the Ag cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ModeHalfStatementPfB.lean#L133-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ModeHalfStatementPfB.lean#L133-L137

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB
open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter ModeHalfA ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.Ag_cont (p0 : ℕ) (hp : p0 ≤ r) : Continuous (Ag p0 hp) := by sorry
