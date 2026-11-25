-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramFlowTransform_mt_y
-- name    : ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform.mt_y
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:17:48.391539+00:00
-- url     : https://prove2.me/theorems/6bcc7369-bb17-4fb2-94c5-9117432bc295
-- title:
--   Gram Flow Transform: mt y
-- statement:
--   The Gram Flow Transform construction uses the mt y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramFlowTransform.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramFlowTransform.lean#L39-L42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramFlowTransform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E}

theorem ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform.mt_y {n : ℕ} (f : Fin n → Fin r → ℂ) (e : Fin r → ℂ) :
    GramDeterminantReal.mt τ G f e = ∑ b, yv τ G f e b * conj (cv τ G f e b) := by sorry
