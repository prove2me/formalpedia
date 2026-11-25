-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_integrableOn_fj
-- name    : ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.integrableOn_fj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:27:07.117192+00:00
-- url     : https://prove2.me/theorems/3557f956-2b02-45c5-8a6a-4e18d0d59302
-- title:
--   Bounded Section Algebra: integrable On fj
-- statement:
--   The Bounded Section Algebra construction uses the integrable On fj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BoundedSectionAlgebra.lean#L108-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BoundedSectionAlgebra.lean#L108-L174

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.integrableOn_fj {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsBddSec la P) {ξ : Fin r → E}
    (hξ : herm X.Gm ξ ξ = 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ν : X.Ψ → ℝ) {D : Set (X.Ψ → ℝ)}
    (hD : volume D < ⊤) :
    IntegrableOn (fun s : X.Ψ → ℝ => P (X.flow ξ (fun τ => (s τ : ℂ)) x) *
      cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)) D := by sorry
