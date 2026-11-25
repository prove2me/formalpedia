-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_IntegralModuleBases_sum_lt_le
-- name    : ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.sum_lt_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:56:27.151192+00:00
-- url     : https://prove2.me/theorems/4ef76235-2481-5d1c-a6c8-b47eee65e645
-- title:
--   Integral Module Bases: sum lt le
-- statement:
--   The Integral Module Bases construction uses the sum lt le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/IntegralModuleBases/NormGsoSqLeTwoPowMulOfValEqAdd.lean#L34-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/IntegralModuleBases/NormGsoSqLeTwoPowMulOfValEqAdd.lean#L34-L54

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

theorem ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.sum_lt_le (b : Fin d → E) (hr : IsRed b) (i : Fin d) :
    ∑ j ∈ univ.filter (fun j : Fin d => j < i), ‖gs b j‖ ^ 2 ≤
      (2 * 2 ^ i.val - 2) * ‖gs b i‖ ^ 2 := by sorry
