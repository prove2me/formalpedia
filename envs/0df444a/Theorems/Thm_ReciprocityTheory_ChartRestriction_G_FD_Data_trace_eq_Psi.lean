-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_trace_eq_Psi
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.trace_eq_Psi
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:12:44.48449+00:00
-- url     : https://prove2.me/theorems/8186a300-aeae-4808-af2d-08dab22bc334
-- title:
--   Data: trace eq Psi
-- statement:
--   The Data construction uses the trace eq Psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ConjugateConjugate.lean#L73-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ConjugateConjugate.lean#L73-L81

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.trace_eq_Psi (y : E) :
    ((Algebra.trace ℚ E y : ℚ) : ℂ) = ∑ τ : X.Ψ, (τ.1 y + conj (τ.1 y)) := by sorry
