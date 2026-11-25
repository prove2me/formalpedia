-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_inv_mul_inv_eq_of_eq_mul
-- name    : ReciprocityTheory.ChartRestriction.L1.inv_mul_inv_eq_of_eq_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:45:10.95013+00:00
-- url     : https://prove2.me/theorems/d25d7865-2a6b-4357-91d6-f0e7c0fef3b9
-- title:
--   L1: inv mul inv eq of eq mul
-- statement:
--   The L1 construction uses the inv mul inv eq of eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgFinA.lean#L109-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgFinA.lean#L109-L113

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SemilinNormPowSubPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgFinA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
omit [IsUltrametricDist K] [CharZero K]

theorem ReciprocityTheory.ChartRestriction.L1.inv_mul_inv_eq_of_eq_mul (c ε t x : K) (hc : c ≠ 0) (h : ε = c * t) :
    x⁻¹ * t⁻¹ = ε⁻¹ * (c / x) := by sorry
