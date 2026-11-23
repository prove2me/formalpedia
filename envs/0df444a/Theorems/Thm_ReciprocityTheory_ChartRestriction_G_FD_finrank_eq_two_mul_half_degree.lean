-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_finrank_eq_two_mul_half_degree
-- name    : ReciprocityTheory.ChartRestriction.G.FD.finrank_eq_two_mul_half_degree
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:25:17.728897+00:00
-- url     : https://prove2.me/theorems/ae3fff69-c7b2-4b9e-b1c2-a41d2aefa391
-- title:
--   FD: finrank eq two mul half degree
-- statement:
--   The FD construction uses the finrank eq two mul half degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FinrankEqTwoMulHalfDegree.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FinrankEqTwoMulHalfDegree.lean#L12-L16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankEqTwoMulHalfDegree
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

theorem ReciprocityTheory.ChartRestriction.G.FD.finrank_eq_two_mul_half_degree : (Module.finrank ℚ E : ℝ) = 2 * (fdeg E : ℝ) := by sorry
