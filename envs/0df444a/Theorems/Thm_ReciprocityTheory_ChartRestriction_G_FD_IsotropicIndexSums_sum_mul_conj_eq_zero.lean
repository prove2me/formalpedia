-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IsotropicIndexSums_sum_mul_conj_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums.sum_mul_conj_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:57.729744+00:00
-- url     : https://prove2.me/theorems/23adbb73-17a7-5c0d-900e-760478369751
-- title:
--   Isotropic Index Sums: sum mul conj eq zero
-- statement:
--   The Isotropic Index Sums construction uses the sum mul conj eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicIndexSums.lean#L85-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicIndexSums.lean#L85-L91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsPerpHermitianReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicIndexSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

theorem ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums.sum_mul_conj_eq_zero {n : ℕ} {c : Fin n → ℂ} (h : ∑ a, c a * conj (c a) = 0) : c = 0 := by sorry
