-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_lead_pos
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.lead_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:34.886405+00:00
-- url     : https://prove2.me/theorems/3304f898-3d61-4fa4-9542-9e68fc02f2d1
-- title:
--   GGC: lead pos
-- statement:
--   The GGC construction uses the lead pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L91-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L91-L111

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConnA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {r : ℕ} (p0 : ℕ)
variable {p0}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.lead_pos {y : Matrix (Fin r) (Fin r) ℂ} (h : Ok p0 y) (i : ℕ) (hi : i ≤ r) :
    0 < (∏ a ∈ Finset.range i, (if a < p0 then (1 : ℝ) else -1)) *
      ((Gy p0 y).submatrix (Fin.castLE hi) (Fin.castLE hi)).det.re := by sorry
