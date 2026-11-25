-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PeriodLatticeMembership_Om_open
-- name    : ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership.Om_open
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:20:42.534434+00:00
-- url     : https://prove2.me/theorems/d1e76b20-b606-4800-936c-7732b24ce8d4
-- title:
--   Period Lattice Membership: Om open
-- statement:
--   The Period Lattice Membership construction uses the Om open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientConvolutionOfSubCoefficients.lean#L211-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientConvolutionOfSubCoefficients.lean#L211-L231

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

theorem ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership.Om_open (ξ : Fin r → E) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ) :
    IsOpen (Om ξ x ω) := by sorry
