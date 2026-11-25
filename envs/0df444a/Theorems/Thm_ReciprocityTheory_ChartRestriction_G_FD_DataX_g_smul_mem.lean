-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DataX_g_smul_mem
-- name    : ReciprocityTheory.ChartRestriction.G.FD.DataX.g_smul_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:27:49.648802+00:00
-- url     : https://prove2.me/theorems/82efe737-80ed-4e00-8921-dbc04ca98e44
-- title:
--   Data X: g smul mem
-- statement:
--   The Data X construction uses the g smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscrMulHermitianIntegral.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscrMulHermitianIntegral.lean#L75-L77

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

theorem ReciprocityTheory.ChartRestriction.G.FD.DataX.g_smul_mem {y : Fin r → E} (hy : y ∈ X.Λ) : (X.g : E) • y ∈ X.Λ := by sorry
