-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_aeval_eq_pow_mul_deh
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.aeval_eq_pow_mul_deh
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:41.150835+00:00
-- url     : https://prove2.me/theorems/f8127e8e-a7ec-41d7-acce-6edf3231e31e
-- title:
--   Fib: aeval eq pow mul deh
-- statement:
--   The Fib construction uses the aeval eq pow mul deh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStA.lean#L59-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStA.lean#L59-L66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.aeval_eq_pow_mul_deh {ι S : Type*} [Fintype ι] [Field S] (v : ι → S) (i₀ : ι)
    (hv : v i₀ ≠ 0) {n : ℕ} {f : MvPolynomial ι ℤ} (hf : f.IsHomogeneous n) :
    aeval v f = v i₀ ^ n * deh v i₀ f := by sorry
