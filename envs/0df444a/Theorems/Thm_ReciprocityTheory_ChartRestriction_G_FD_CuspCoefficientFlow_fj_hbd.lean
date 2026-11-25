-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CuspCoefficientFlow_fj_hbd
-- name    : ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.fj_hbd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:13:57.246475+00:00
-- url     : https://prove2.me/theorems/f925e4e7-f332-48e3-a03f-4bb95d17b837
-- title:
--   Cusp Coefficient Flow: fj hbd
-- statement:
--   The Cusp Coefficient Flow construction uses the fj hbd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CuspCoefficientFlow.lean#L197-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CuspCoefficientFlow.lean#L197-L225

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.fj_hbd (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P) {ξ : Fin r → E}
    (hξ : X.IsIso ξ) : ∀ x0 ∈ X.dom, ∃ ρ > 0, ∃ C, closedBall x0 ρ ⊆ X.dom ∧
      ∀ t : X.Ψ → ℝ, ∀ z ∈ closedBall x0 ρ, ‖P (flowL X ξ t z)‖ ≤ C := by sorry
