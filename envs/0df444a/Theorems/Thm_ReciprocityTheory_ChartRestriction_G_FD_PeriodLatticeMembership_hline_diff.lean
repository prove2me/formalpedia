-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PeriodLatticeMembership_hline_diff
-- name    : ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership.hline_diff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:21:39.828915+00:00
-- url     : https://prove2.me/theorems/db89f8ea-b301-5ddb-b1fd-e32500a002d8
-- title:
--   Period Lattice Membership: hline diff
-- statement:
--   The Period Lattice Membership construction uses the hline diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientConvolutionOfSubCoefficients.lean#L354-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientConvolutionOfSubCoefficients.lean#L354-L367

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientConvolutionOfSubCoefficients
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates.Y
  ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} (X : Data E r)
variable {X}

theorem ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership.hline_diff {P : Frame X.Ψ r → ℂ} (hP : DifferentiableOn ℂ P X.dom) {ξ : Fin r → E}
    (hξ : herm X.Gm ξ ξ = 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ) :
    DifferentiableOn ℂ (hline X P ξ x ω) (tube (Fintype.card X.Ψ) (Om ξ x ω)) := by sorry
