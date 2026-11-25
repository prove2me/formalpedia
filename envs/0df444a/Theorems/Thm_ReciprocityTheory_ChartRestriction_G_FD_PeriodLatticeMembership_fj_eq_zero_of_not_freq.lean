-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PeriodLatticeMembership_fj_eq_zero_of_not_freq
-- name    : ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership.fj_eq_zero_of_not_freq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:22:06.858543+00:00
-- url     : https://prove2.me/theorems/a9fcbc4c-09cd-5cfb-a609-c237c12f0e60
-- title:
--   Period Lattice Membership: fj eq zero of not freq
-- statement:
--   The Period Lattice Membership construction uses the fj eq zero of not freq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientConvolutionOfSubCoefficients.lean#L100-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientConvolutionOfSubCoefficients.lean#L100-L103

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

theorem ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership.fj_eq_zero_of_not_freq (la : Wt X.Ψ r) (ξ : Fin r → E) (ν : X.Ψ → ℝ) (P : Frame X.Ψ r → ℂ)
    (x : Frame X.Ψ r) (h : ¬ ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k) :
    X.fj la ξ ν P x = 0 := by sorry
