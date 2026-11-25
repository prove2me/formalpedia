-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_IntegralModuleBases_norm_sq_le_pow_gs
-- name    : ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.norm_sq_le_pow_gs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:23.830797+00:00
-- url     : https://prove2.me/theorems/e71bbb6e-73dc-4bc3-96bc-64955dfdeb18
-- title:
--   Integral Module Bases: norm sq le pow gs
-- statement:
--   The Integral Module Bases construction uses the norm sq le pow gs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/IntegralModuleBases/NormGsoSqLeTwoPowMulOfValEqAdd.lean#L64-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/IntegralModuleBases/NormGsoSqLeTwoPowMulOfValEqAdd.lean#L64-L91

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
open Finset InnerProductSpace ReciprocityTheory.ReducedBases.T2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.norm_sq_le_pow_gs (b : Fin d → E) (hr : IsRed b) (i : Fin d) :
    ‖b i‖ ^ 2 ≤ 2 ^ i.val * ‖gs b i‖ ^ 2 := by sorry
