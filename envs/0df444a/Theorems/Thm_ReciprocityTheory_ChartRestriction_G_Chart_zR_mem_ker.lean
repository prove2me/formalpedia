-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_zR_mem_ker
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.zR_mem_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:12.825936+00:00
-- url     : https://prove2.me/theorems/c2e1dda2-63e6-4450-be07-cf90da2aee43
-- title:
--   Chart: z R mem ker
-- statement:
--   The Chart construction uses the z R mem ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/SpanXLeKerAevalZero.lean#L114-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/SpanXLeKerAevalZero.lean#L114-L115

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open MvPolynomial
variable (R : Type) [CommRing R]
variable {R}
variable (R)
variable {R}

theorem ReciprocityTheory.ChartRestriction.G.Chart.zR_mem_ker {κ : Type} (m : ℕ) (j : κ) : zR (R := R) m j ∈ RingHom.ker (jetAug R κ m) := by sorry
