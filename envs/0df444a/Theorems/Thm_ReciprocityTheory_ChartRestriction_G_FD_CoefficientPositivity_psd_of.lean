-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CoefficientPositivity_psd_of
-- name    : ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity.psd_of
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:12:33.596021+00:00
-- url     : https://prove2.me/theorems/b6683877-67a5-5538-ba05-10de2191a9d1
-- title:
--   Coefficient Positivity: psd of
-- statement:
--   The Coefficient Positivity construction uses the psd of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientPositivity.lean#L105-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientPositivity.lean#L105-L119

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

theorem ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity.psd_of (X : Data E r) (u : Fin 2 → Fin r → E) (hu : IsIsoPair X.Gm u) (la : Wt X.Ψ r)
    (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (hχ : IsHermFam χ) (F : Frame X.Ψ r → ℂ)
    (hF : DifferentiableOn ℂ F X.dom)
    (hZ : ∀ b, IsHermFam b → ∀ x ∈ X.dom, F (X.Zb u b x) = cexp (4 * Real.pi * I * X.pairR χ b) * F x)
    (C : ℝ) (hC : ∀ y ∈ X.dom, X.pnorm la F y ≤ C) {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom)
    (hF0 : F x0 ≠ 0) (τ0 : X.Ψ) : (Matrix.of (χ τ0)).PosSemidef := by sorry
