-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptSumL_good
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.ptSumL_good
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:36:36.224486+00:00
-- url     : https://prove2.me/theorems/a3882b03-59e0-4d22-8671-d3284ca3416f
-- title:
--   Sh: pt Sum L good
-- statement:
--   The Sh construction uses the pt Sum L good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtRescaleGood.lean#L169-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtRescaleGood.lean#L169-L172

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.ptSumL_good (G : LogFGL v d) {τ : Type*} :
    ∀ l : List (Fin d → MvPowerSeries τ C), (∀ x ∈ l, PTGood v x) → PTGood v (ptSumL G l)
  := by sorry
