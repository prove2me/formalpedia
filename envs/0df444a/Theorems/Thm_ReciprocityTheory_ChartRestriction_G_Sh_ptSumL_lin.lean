-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptSumL_lin
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.ptSumL_lin
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:51.51684+00:00
-- url     : https://prove2.me/theorems/f71add0b-7fa3-580b-aa73-28ca1b43e10a
-- title:
--   Sh: pt Sum L lin
-- statement:
--   The Sh construction uses the pt Sum L lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtRescaleGood.lean#L202-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtRescaleGood.lean#L202-L210

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.ptSumL_lin (G : LogFGL v d) {τ : Type*} :
    ∀ l : List (Fin d → MvPowerSeries τ C), (∀ x ∈ l, ∀ a, constantCoeff (x a) = 0) →
      ∀ a t, coeff (Finsupp.single t 1) (ptSumL G l a) =
        (l.map fun x => coeff (Finsupp.single t 1) (x a)).sum
  := by sorry
