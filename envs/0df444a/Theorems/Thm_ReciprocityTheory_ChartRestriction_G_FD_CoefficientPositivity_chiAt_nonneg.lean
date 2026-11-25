-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CoefficientPositivity_chiAt_nonneg
-- name    : ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity.chiAt_nonneg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:13:23.597047+00:00
-- url     : https://prove2.me/theorems/2b430807-3fee-4cbd-adc9-ed67f0bafe16
-- title:
--   Coefficient Positivity: chi At nonneg
-- statement:
--   The Coefficient Positivity construction uses the chi At nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientPositivity.lean#L18-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientPositivity.lean#L18-L103

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeMinorExistence
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExponentialGrowthExclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bNormHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientPositivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
  ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity.chiAt_nonneg (X : Data E r) (u : Fin 2 → Fin r → E) (hu : IsIsoPair X.Gm u) (la : Wt X.Ψ r)
    (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (F : Frame X.Ψ r → ℂ) (hF : DifferentiableOn ℂ F X.dom)
    (hZ : ∀ b, IsHermFam b → ∀ x ∈ X.dom, F (X.Zb u b x) = cexp (4 * Real.pi * I * X.pairR χ b) * F x)
    (C : ℝ) (hC : ∀ y ∈ X.dom, X.pnorm la F y ≤ C) {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom)
    (hF0 : F x0 ≠ 0) (a : X.Ψ → Fin 2 → ℂ) (ha : ∀ τ, a τ ≠ 0) (τ0 : X.Ψ) :
    0 ≤ (X.chiAt χ a τ0).re := by sorry
