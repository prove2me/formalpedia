-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.jet_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:28:09.796733+00:00
-- url     : https://prove2.me/theorems/7e1bd656-3f8b-403a-9d8c-5dd17968e1c7
-- title:
--   Chart: jet ext
-- statement:
--   The Chart construction uses the jet ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/SpanXLeKerAevalZero.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/SpanXLeKerAevalZero.lean#L47-L52

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.jet_ext {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra R A] {ψ₁ ψ₂ : JetR R κ m →ₐ[R] A}
    (h : ∀ j, ψ₁ (zR (R := R) m j) = ψ₂ (zR (R := R) m j)) : ψ₁ = ψ₂ := by sorry
