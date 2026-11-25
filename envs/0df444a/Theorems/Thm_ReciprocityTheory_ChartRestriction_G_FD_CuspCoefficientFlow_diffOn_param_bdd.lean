-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CuspCoefficientFlow_diffOn_param_bdd
-- name    : ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.diffOn_param_bdd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:16:48.815697+00:00
-- url     : https://prove2.me/theorems/61a15e64-d2ab-5318-bf64-40087e9e63fc
-- title:
--   Cusp Coefficient Flow: diff On param bdd
-- statement:
--   The Cusp Coefficient Flow construction uses the diff On param bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CuspCoefficientFlow.lean#L68-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CuspCoefficientFlow.lean#L68-L126

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
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [MeasurableSpace F] [BorelSpace F] {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.diffOn_param_bdd {K : Set (ι → ℝ)} (hKv : volume K < ⊤)
    (A : (ι → ℝ) → F →L[ℂ] F) (hA : Continuous A) {U : Set F} (hU : IsOpen U)
    (hAU : ∀ t, ∀ x ∈ U, A t x ∈ U) (G : F → ℂ) (hG : DifferentiableOn ℂ G U)
    (e : (ι → ℝ) → ℂ) (he : Continuous e) (he1 : ∀ t, ‖e t‖ ≤ 1)
    (hbd : ∀ x0 ∈ U, ∃ ρ > 0, ∃ C, closedBall x0 ρ ⊆ U ∧
      ∀ t, ∀ z ∈ closedBall x0 ρ, ‖G (A t z)‖ ≤ C) :
    DifferentiableOn ℂ (fun x => ∫ t in K, G (A t x) * e t) U := by sorry
