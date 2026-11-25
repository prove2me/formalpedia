-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_VanishPf_cpt_zero
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.cpt_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:02:56.614339+00:00
-- url     : https://prove2.me/theorems/2fd67dcd-996e-4321-8c0e-8aa983f8f638
-- title:
--   Vanish Pf: cpt zero
-- statement:
--   The Vanish Pf construction uses the cpt zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/VanishAtSStatementPf.lean#L94-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/VanishAtSStatementPf.lean#L94-L103

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_MvBlowup
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_VanishAtSStatementPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
  Filter Asymptotics
open scoped ENNReal
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.cpt_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x1 : Frame X.Ψ r) : cpt X x1 0 = x1 := by sorry
