-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_iteratedFDeriv_single_column
-- name    : ReciprocityTheory.ChartRestriction.G.I2.iteratedFDeriv_single_column
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:28.897352+00:00
-- url     : https://prove2.me/theorems/7ab56e1b-066d-4eff-9c7d-abf4bf760983
-- title:
--   I2: iterated FDeriv single column
-- statement:
--   The I2 construction uses the iterated FDeriv single column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelA.lean#L152-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelA.lean#L152-L159

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.I2.iteratedFDeriv_single_column {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {c : ℕ} {g : V → ℂ}
    (hg : ContDiff ℂ c g) (x : Fin c → V) :
    iteratedFDeriv ℂ c (fun w : Fin 1 → V => g (w 0)) 0 (fun k _ => x k) = iteratedFDeriv ℂ c g 0 x := by sorry
