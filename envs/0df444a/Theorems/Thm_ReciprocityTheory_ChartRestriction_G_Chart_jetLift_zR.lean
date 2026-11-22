-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.jetLift_zR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:35.717311+00:00
-- url     : https://prove2.me/theorems/6f79d647-d272-45ce-ba72-8330b62c48ba
-- title:
--   Chart: jet Lift z R
-- statement:
--   The Chart construction uses the jet Lift z R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/SpanXLeKerAevalZero.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/SpanXLeKerAevalZero.lean#L69-L73

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.jetLift_zR {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra R A] (J : Ideal A)
    (hJ : J ^ (m + 1) = ⊥) (b : κ → A) (hb : ∀ j, b j ∈ J) (j : κ) :
    jetLift R J hJ b hb (zR m j) = b j := by sorry
