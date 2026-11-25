-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_IntegralModuleBases_norm_gso_sq_le_two_pow_mul_of_val_eq_add
-- name    : ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.norm_gso_sq_le_two_pow_mul_of_val_eq_add
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:56:19.275888+00:00
-- url     : https://prove2.me/theorems/4786f5ab-2ad0-5cba-9522-d276e3a1aa28
-- title:
--   Integral Module Bases: norm gso sq le two pow mul of val eq add
-- statement:
--   The Integral Module Bases construction uses the norm gso sq le two pow mul of val eq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/IntegralModuleBases/NormGsoSqLeTwoPowMulOfValEqAdd.lean#L12-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/IntegralModuleBases/NormGsoSqLeTwoPowMulOfValEqAdd.lean#L12-L27

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

theorem ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.norm_gso_sq_le_two_pow_mul_of_val_eq_add (b : Fin d → E) (hr : IsRed b) :
    ∀ (n : ℕ) (i j : Fin d), i.val = j.val + n → ‖gs b j‖ ^ 2 ≤ 2 ^ n * ‖gs b i‖ ^ 2 := by sorry
