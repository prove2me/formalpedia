-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_fj_mul_zero
-- name    : ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_mul_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:15:32.885243+00:00
-- url     : https://prove2.me/theorems/9cb1a66a-6436-4ee3-af71-ce79e13cd1eb
-- title:
--   Bounded Section Algebra: fj mul zero
-- statement:
--   The Bounded Section Algebra construction uses the fj mul zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BoundedSectionAlgebra.lean#L281-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BoundedSectionAlgebra.lean#L281-L300

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

theorem ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_mul_zero (h3d : ModerateCoefficientPositivity (E := E)) (h3e : CoefficientConvolution (E := E)) {la la' : Wt X.Ψ r}
    {P Q : Frame X.Ψ r → ℂ} (hP : X.IsBddSec la P) (hQ : X.IsBddSec la' Q) {ξ : Fin r → E}
    (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ν : X.Ψ → ℝ)
    (hvan : ∀ ν' : X.Ψ → ℝ, (∀ τ, 0 ≤ ν' τ) → (∀ τ, 0 ≤ ν τ - ν' τ) → X.fj la ξ ν' P x = 0) :
    X.fj (la + la') ξ ν (P * Q) x = 0 := by sorry
