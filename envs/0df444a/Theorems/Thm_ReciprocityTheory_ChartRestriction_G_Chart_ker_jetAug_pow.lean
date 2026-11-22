-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.ker_jetAug_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:44:36.481105+00:00
-- url     : https://prove2.me/theorems/ea40642f-d5dc-4e6c-b64c-bbd43b2e8234
-- title:
--   Chart: ker jet Aug pow
-- statement:
--   The Chart construction uses the ker jet Aug pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/SpanXLeKerAevalZero.lean#L94-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/SpanXLeKerAevalZero.lean#L94-L109

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.ker_jetAug_pow (κ : Type) (m : ℕ) : (RingHom.ker (jetAug R κ m)) ^ (m + 1) = ⊥ := by sorry
