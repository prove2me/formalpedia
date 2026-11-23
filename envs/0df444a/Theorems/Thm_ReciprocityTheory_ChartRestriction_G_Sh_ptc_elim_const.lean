-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptc_elim_const
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.ptc_elim_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:13.038682+00:00
-- url     : https://prove2.me/theorems/637ab951-1add-414c-8b91-f7f558c71889
-- title:
--   Sh: ptc elim const
-- statement:
--   The Sh construction uses the ptc elim const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtRescaleGood.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtRescaleGood.lean#L24-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtRescaleGood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Sh.ptc_elim_const {τ : Type*} {x y : Fin d → MvPowerSeries τ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) :
    ∀ s, constantCoeff (Sum.elim x y s) = 0 := by sorry
