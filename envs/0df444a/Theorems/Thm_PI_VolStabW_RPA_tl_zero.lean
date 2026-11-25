-- Prove2me | Theorems.Thm_PI_VolStabW_RPA_tl_zero
-- name    : PI.VolStabW.RPA.tl_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:41:28.574247+00:00
-- url     : https://prove2.me/theorems/fded382d-06f0-5740-ac15-5396c5117d10
-- title:
--   RPA: tl zero
-- statement:
--   The RPA construction uses the tl zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/ESSymmApply.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/ESSymmApply.lean#L59-L61

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ESSymmApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.RPA
open MeasureTheory Filter Finset
open scoped NNReal ENNReal
variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable (m : ∀ i, Measure (W i)) (L : ∀ i, Set (W i))
variable {m L}

theorem PI.VolStabW.RPA.tl_zero [DecidableEq ι] (hT : TailH m L) {S : Finset ι} {i : ι} (hi : i ∉ S)
    (h0 : am m L i = 0) : tl m L S = 0 := by sorry
