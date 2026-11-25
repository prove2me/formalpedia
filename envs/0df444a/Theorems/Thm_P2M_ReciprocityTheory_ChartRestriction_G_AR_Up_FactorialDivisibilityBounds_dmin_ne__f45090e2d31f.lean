-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FactorialDivisibilityBounds_dmin_ne__f45090e2d31f
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FactorialDivisibilityBounds_dmin_ne__f45090e2d31f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:13:58.9208+00:00
-- url     : https://prove2.me/theorems/aeda5819-4619-5765-9c6e-d91e8fa8e5c2
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up Factorial Divisibility Bounds dmin ne  f45090e2d31f: P2 M Reciprocity Theory Chart Restriction G AR Up Factorial Divisibility Bounds dmin ne  f45090e2
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up Factorial Divisibility Bounds dmin ne  f45090e2d31f construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up Factorial Divisibility Bounds dmin ne  f45090e2d31f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/CuspStatementPf.lean#L64-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/CuspStatementPf.lean#L64-L67

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FactorialDivisibilityBounds_dmin_ne__f45090e2d31f (j : Fin (r + 1)) : dmin X.Gm x τ j ≠ 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«FactorialDivisibilityBounds».«dmin_ne'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FactorialDivisibilityBounds_dmin_ne__f45090e2d31f
