-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientDomain_norm_fderiv_le
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.norm_fderiv_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:15:39.626794+00:00
-- url     : https://prove2.me/theorems/2277b5bd-623d-4277-90af-f857aa944209
-- title:
--   Fourier Coefficient Domain: norm fderiv le
-- statement:
--   The Fourier Coefficient Domain construction uses the norm fderiv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientDomain.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientDomain.lean#L15-L18

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
import Definitions.Def_Lemmata_GeneralBFactBisForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology
noncomputable section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.norm_fderiv_le {U : Set F} (hU : IsOpen U) {G : F → ℂ} (hG : DifferentiableOn ℂ G U)
    {y : F} {R C : ℝ} (hR : 0 < R) (hball : closedBall y R ⊆ U)
    (hC : ∀ z ∈ closedBall y R, ‖G z‖ ≤ C) : ‖fderiv ℂ G y‖ ≤ C / R := by sorry
