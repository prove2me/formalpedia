-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfB_sf_smul_right
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.sf_smul_right
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:45:56.136477+00:00
-- url     : https://prove2.me/theorems/38a565b7-074e-54f6-a06a-ff7ce6a4f829
-- title:
--   Mode Half B: sf smul right
-- statement:
--   The Mode Half B construction uses the sf smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ModeHalfStatementPfB.lean#L87-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ModeHalfStatementPfB.lean#L87-L90

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.sf_smul_right (p0 : ℕ) (c : ℝ) (α β : Fin r → ℂ) :
    sf p0 α ((c : ℂ) • β) = c * sf p0 α β := by sorry
