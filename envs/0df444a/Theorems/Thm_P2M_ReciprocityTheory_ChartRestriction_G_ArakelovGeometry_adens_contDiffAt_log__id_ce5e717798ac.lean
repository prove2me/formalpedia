-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_contDiffAt_log__id_ce5e717798ac
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_contDiffAt_log__id_ce5e717798ac
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:29.140277+00:00
-- url     : https://prove2.me/theorems/f64b8a07-9653-45e9-8133-d07264ff0dc2
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry adens cont Diff At log  id ce5e717798ac: P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry adens cont Diff At log  id ce5e7177
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry adens cont Diff At log  id ce5e717798ac construction uses the P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry adens cont Diff At log  id ce5e717798ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStC.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStC.lean#L69-L73

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
open scoped ComplexOrder
variable {J : Type} [Fintype J] {D : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_contDiffAt_log__id_ce5e717798ac {m : ConeMetric ℂ J} (hsm : IsSmoothMetric m) {z : J → ℂ}
    (hne : z ≠ 0) : ContDiffAt ℝ 2 (fun w => Real.log (m.ρ w)) z := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«ArakelovGeometry».«adens_contDiffAt_logρ_id» := P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_contDiffAt_log__id_ce5e717798ac
