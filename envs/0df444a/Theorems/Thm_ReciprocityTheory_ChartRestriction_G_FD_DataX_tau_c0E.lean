-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DataX_tau_c0E
-- name    : ReciprocityTheory.ChartRestriction.G.FD.DataX.tau_c0E
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:13:33.93928+00:00
-- url     : https://prove2.me/theorems/c391256a-ceac-460d-b8d7-2eca46cd3c93
-- title:
--   Data X: tau c0 E
-- statement:
--   The Data X construction uses the tau c0 E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscrMulHermitianIntegral.lean#L127-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscrMulHermitianIntegral.lean#L127-L131

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscrMulHermitianIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.DataX
variable {r : ℕ} (X : DataX E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.DataX.tau_c0E (τ : E →+* ℂ) : τ X.c0E = ((((X.g * dEnat E : ℕ) : ℝ) / 2 : ℝ) : ℂ) := by sorry
