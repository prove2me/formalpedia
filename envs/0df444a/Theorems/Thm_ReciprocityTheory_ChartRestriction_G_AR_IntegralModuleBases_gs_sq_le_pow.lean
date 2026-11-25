-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_IntegralModuleBases_gs_sq_le_pow
-- name    : ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.gs_sq_le_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:56:51.582261+00:00
-- url     : https://prove2.me/theorems/dbaad6b8-1acb-422d-81ad-ea0c18996735
-- title:
--   Integral Module Bases: gs sq le pow
-- statement:
--   The Integral Module Bases construction uses the gs sq le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/IntegralModuleBases/NormGsoSqLeTwoPowMulOfValEqAdd.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/IntegralModuleBases/NormGsoSqLeTwoPowMulOfValEqAdd.lean#L29-L32

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

theorem ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.gs_sq_le_pow (b : Fin d → E) (hr : IsRed b) (i j : Fin d) (h : j ≤ i) :
    ‖gs b j‖ ^ 2 ≤ 2 ^ (i.val - j.val) * ‖gs b i‖ ^ 2 := by sorry
