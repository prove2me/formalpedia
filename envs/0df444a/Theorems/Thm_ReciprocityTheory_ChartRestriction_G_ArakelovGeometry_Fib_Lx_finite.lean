-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Lx_finite
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Lx_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:44.733231+00:00
-- url     : https://prove2.me/theorems/54da280e-7f4a-49dd-804f-ea2a106c8000
-- title:
--   Fib: Lx finite
-- statement:
--   The Fib construction uses the Lx finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStD.lean#L211-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStD.lean#L211-L218

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module IntermediateField
variable {Ω : Type*} [Field Ω] [CharZero Ω] {ι : Type} [Fintype ι] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Lx_finite (x : ι → Ω) (e : Fin (D + 1) → ι) (h : IsProjFrame x e) :
    FiniteDimensional (fnField (x ∘ e)) (Lx x e) := by sorry
