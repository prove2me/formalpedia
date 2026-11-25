-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CoefficientPositivity_fz_zero_of_inv
-- name    : ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity.fz_zero_of_inv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:16:40.885179+00:00
-- url     : https://prove2.me/theorems/b01ee691-45b2-4914-a561-d4bc53ef9dc9
-- title:
--   Coefficient Positivity: fz zero of inv
-- statement:
--   The Coefficient Positivity construction uses the fz zero of inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientPositivity.lean#L133-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientPositivity.lean#L133-L231

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

theorem ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity.fz_zero_of_inv (X : Data E r) (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (g : ℕ) (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (hcond : IsHermFam χ ∧ X.IsFreqZ g χ)
    (hωex : ∃ ω, X.IsLZBasis g ω) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hPc : ContinuousOn P X.dom)
    (C : ℝ) (hC : ∀ y ∈ X.dom, X.pnorm la P y ≤ C) (ξ : Fin r → E) (hξ : herm X.Gm ξ ξ = 0)
    (a : X.Ψ → Fin 2 → ℂ) (hemb : ∀ τ : X.Ψ, Data.emb τ.1 ξ = X.uvec u a τ)
    (hcusp : ∀ y ∈ X.dom, X.fj la ξ 0 P y = 0) {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom)
    (hinv : ∀ s : X.Ψ → ℝ, X.fz u g χ P (X.flow ξ (fun τ => (s τ : ℂ)) x0) = X.fz u g χ P x0) :
    X.fz u g χ P x0 = 0 := by sorry
