-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_psIsInt_iff
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.psIsInt_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:50.402001+00:00
-- url     : https://prove2.me/theorems/5fa3074f-16a3-45a9-9d66-a404d949e955
-- title:
--   PTb: ps Is Int iff
-- statement:
--   The PTb construction uses the ps Is Int iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/TangentEqLcZero.lean#L69-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/TangentEqLcZero.lean#L69-L76

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.psIsInt_iff {v : AddValuation C (WithTop ℝ)} {f : PowerSeries C} :
    PsIsInt v f ↔ MvIsInt v (σ := Unit) f := by sorry
