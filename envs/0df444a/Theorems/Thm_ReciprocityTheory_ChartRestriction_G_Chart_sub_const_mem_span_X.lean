-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_sub_const_mem_span_X
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.sub_const_mem_span_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:52.613958+00:00
-- url     : https://prove2.me/theorems/532d44bc-9a2c-4584-9b86-3e40a6ec6c9d
-- title:
--   Chart: sub const mem span X
-- statement:
--   The Chart construction uses the sub const mem span X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/SpanXLeKerAevalZero.lean#L75-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/SpanXLeKerAevalZero.lean#L75-L92

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.sub_const_mem_span_X {κ : Type} (p : MvPolynomial κ R) :
    p - MvPolynomial.C (MvPolynomial.aeval (fun _ : κ => (0 : R)) p) ∈
      Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R)) := by sorry
