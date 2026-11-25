-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfB_Ms_contAt
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.Ms_contAt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:51:26.447912+00:00
-- url     : https://prove2.me/theorems/4cc2c98d-9928-47e1-8e44-2c67477f8dc1
-- title:
--   Mode Half B: Ms cont At
-- statement:
--   The Mode Half B construction uses the Ms cont At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ModeHalfStatementPfB.lean#L151-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ModeHalfStatementPfB.lean#L151-L171

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.Ms_contAt (p0 : ℕ) (hp : p0 ≤ r) (v0 : Fin r → ℂ) :
    ContinuousAt (fun p : (Fin r → Fin r → ℂ) × (Fin r → ℂ) => Ms p0 hp p.1 p.2) (Nid r, v0) := by sorry
