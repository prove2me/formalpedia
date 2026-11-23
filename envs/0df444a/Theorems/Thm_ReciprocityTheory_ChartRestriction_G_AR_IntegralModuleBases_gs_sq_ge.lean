-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_IntegralModuleBases_gs_sq_ge
-- name    : ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.gs_sq_ge
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:02.359023+00:00
-- url     : https://prove2.me/theorems/0965d7ce-5ad9-4578-85a1-616aab6e2fc9
-- title:
--   Integral Module Bases: gs sq ge
-- statement:
--   The Integral Module Bases construction uses the gs sq ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/IntegralModuleBases/NormGsoSqLeTwoPowMulOfValEqAdd.lean#L93-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/IntegralModuleBases/NormGsoSqLeTwoPowMulOfValEqAdd.lean#L93-L101

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

theorem ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.gs_sq_ge (b : Fin d → E) (hr : IsRed b) (m : ℝ) (hm : ∀ i, m ≤ ‖b i‖ ^ 2) (j : Fin d) :
    m / 2 ^ (d - 1) ≤ ‖gs b j‖ ^ 2 := by sorry
