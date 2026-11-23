-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_exp_mul_conj
-- name    : ReciprocityTheory.ChartRestriction.G.I2.nA_exp_mul_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:11.529406+00:00
-- url     : https://prove2.me/theorems/924ae6eb-11a3-4dd3-babf-a96ab15ab81c
-- title:
--   I2: n A exp mul conj
-- statement:
--   The I2 construction uses the n A exp mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L81-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L81-L82

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section
variable {ι : Type} [Fintype ι]
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.I2.nA_exp_mul_conj (z : ℂ) : cexp z * (starRingEnd ℂ) (cexp z) = ((Real.exp (2 * z.re) : ℝ) : ℂ) := by sorry
