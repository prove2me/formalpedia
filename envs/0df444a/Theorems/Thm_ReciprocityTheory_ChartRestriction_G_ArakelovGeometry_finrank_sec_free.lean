-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_finrank_sec_free
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.finrank_sec_free
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:40.67661+00:00
-- url     : https://prove2.me/theorems/df0ef1d5-35c1-41d3-b74d-38cb74049cae
-- title:
--   Arakelov Geometry: finrank sec free
-- statement:
--   The Arakelov Geometry construction uses the finrank sec free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/SectionModuleEqSpanPow.lean#L201-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/SectionModuleEqSpanPow.lean#L201-L215

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.finrank_sec_free (y : Fin (D + 1) → Ω) (hy : coordIdeal ℤ y = ⊥) (n : ℕ) :
    finrank ℤ (sec ℤ y n) = (n + D).choose D := by sorry
