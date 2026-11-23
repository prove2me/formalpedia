-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_maj_smul
-- name    : ReciprocityTheory.ChartRestriction.G.FD.UnipotentCoefficientShift.maj_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:11.685628+00:00
-- url     : https://prove2.me/theorems/922095a1-026c-4719-8964-2e8d6a78f213
-- title:
--   Unipotent Coefficient Shift: maj smul
-- statement:
--   The Unipotent Coefficient Shift construction uses the maj smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentCoefficientShift.lean#L124-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentCoefficientShift.lean#L124-L142

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.UnipotentCoefficientShift
open NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} {X : Data E r}

theorem ReciprocityTheory.ChartRestriction.G.FD.UnipotentCoefficientShift.maj_smul {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (k : ℝ) (v : Fin r → ℂ) :
    X.maj z τ ((k : ℂ) • v) = k ^ 2 * X.maj z τ v := by sorry
