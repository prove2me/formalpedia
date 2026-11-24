-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coord_ne_zero
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coord_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:42.512824+00:00
-- url     : https://prove2.me/theorems/51f0ebbc-882b-4ec3-a716-396cb765047a
-- title:
--   Fib: coord ne zero
-- statement:
--   The Fib construction uses the coord ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStD.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStD.lean#L12-L18

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_coord_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coord_ne_zero {ι : Type*} (y : ι → Ω) (h : coordIdeal ℤ y = ⊥) (k : ι) : y k ≠ 0 := by sorry
