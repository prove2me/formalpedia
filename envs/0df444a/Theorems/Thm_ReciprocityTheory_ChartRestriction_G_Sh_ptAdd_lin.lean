-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptAdd_lin
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.ptAdd_lin
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:22.281812+00:00
-- url     : https://prove2.me/theorems/749844f9-2ce4-4d18-9e72-3e62e3588b51
-- title:
--   Sh: pt Add lin
-- statement:
--   The Sh construction uses the pt Add lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtRescaleGood.lean#L149-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtRescaleGood.lean#L149-L160

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.ptAdd_lin (G : LogFGL v d) {τ : Type*} {x y : Fin d → MvPowerSeries τ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (a : Fin d)
    (t : τ) :
    coeff (Finsupp.single t 1) (ptAdd G x y a) =
      coeff (Finsupp.single t 1) (x a) + coeff (Finsupp.single t 1) (y a) := by sorry
