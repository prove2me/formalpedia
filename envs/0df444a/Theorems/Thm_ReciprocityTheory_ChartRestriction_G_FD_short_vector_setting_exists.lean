-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_short_vector_setting_exists
-- name    : ReciprocityTheory.ChartRestriction.G.FD.short_vector_setting_exists
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:21:53.41692+00:00
-- url     : https://prove2.me/theorems/8774b89f-8a6b-4d46-b7fb-9c7be5b8197d
-- title:
--   FD: short vector setting exists
-- statement:
--   The FD construction uses the short vector setting exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentVectorEqSmulComponent.lean#L101-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentVectorEqSmulComponent.lean#L101-L113

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankEqTwoMulHalfDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentVectorEqSmulComponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
set_option maxHeartbeats 1000000

theorem ReciprocityTheory.ChartRestriction.G.FD.short_vector_setting_exists {r : ℕ} (X : DataX E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} {ξ : Fin r → E}
    {ν : X.Ψ → ℝ} {c1 w : ℝ} {z0 : Frame X.Ψ r} (hH : ShortVectorHypotheses X la P ξ ν c1 w z0) {x : Fin r → E}
    (hxL : x ∈ X.L') (hxξ : herm X.Gm x ξ = 0) (hxx : herm X.Gm x x = 0) (hxE : ∀ e : E, x ≠ e • ξ) :
    ∃ a, IsotropicFlowSetting X la P ξ ν c1 w z0 x a := by sorry
