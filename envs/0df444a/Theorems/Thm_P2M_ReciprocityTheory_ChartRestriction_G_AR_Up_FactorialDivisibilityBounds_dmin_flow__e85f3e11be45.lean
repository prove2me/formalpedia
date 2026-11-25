-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FactorialDivisibilityBounds_dmin_flow__e85f3e11be45
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FactorialDivisibilityBounds_dmin_flow__e85f3e11be45
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:53.339868+00:00
-- url     : https://prove2.me/theorems/80181c8a-0b63-4894-93d6-9204dde10be2
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up Factorial Divisibility Bounds dmin flow  e85f3e11be45: P2 M Reciprocity Theory Chart Restriction G AR Up Factorial Divisibility Bounds dmin flow  e85f
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up Factorial Divisibility Bounds dmin flow  e85f3e11be45 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up Factorial Divisibility Bounds dmin flow  e85f3e11be45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/CuspStatementPf.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/CuspStatementPf.lean#L59-L62

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FjFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CuspStatementPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
  ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
noncomputable section
open ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} (X : Data E r)
variable (e : X.Ψ → Fin r → ℂ) (he : X.IsIsoV e) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
  (s : X.Ψ → ℂ) (hT : X.flowV e s x ∈ X.dom) (τ : X.Ψ)
include he hx

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FactorialDivisibilityBounds_dmin_flow__e85f3e11be45 (j : Fin (r + 1)) :
    dmin X.Gm (X.flowV e s x) τ j = dmin X.Gm x τ j * ((rho X e s x τ j : ℝ) : ℂ) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«FactorialDivisibilityBounds».«dmin_flow'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FactorialDivisibilityBounds_dmin_flow__e85f3e11be45
