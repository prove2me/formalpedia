-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FactorialDivisibilityBounds_rfac_le
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds.rfac_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:58:41.57693+00:00
-- url     : https://prove2.me/theorems/a978fd5a-dcf0-5e8b-ab09-e1733222af73
-- title:
--   Factorial Divisibility Bounds: rfac le
-- statement:
--   The Factorial Divisibility Bounds construction uses the rfac le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/CuspStatementPf.lean#L113-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/CuspStatementPf.lean#L113-L165

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
include hT

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds.rfac_le (la : Wt X.Ψ r) (hs : 0 ≤ (s τ).im) (hp0 : 0 < X.p0) (hp0r : X.p0 < r)
    (hgap : ∀ i j : Fin r, (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → la τ j ≤ la τ i)
    (hpair : ∀ i0 i1 : Fin r, (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 → la τ i0 < la τ i1) :
    rfac X la x (X.flowV e s x) τ ≤
      Real.exp (-(1 / 2) * Real.log (1 + (s τ).im / X.ttV e x τ)) := by sorry
