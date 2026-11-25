-- Prove2me | Theorems.Thm_PI_VolStabW_FiniteFieldSplitting_ffH_fst
-- name    : PI.VolStabW.FiniteFieldSplitting.ffH_fst
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:37:11.713818+00:00
-- url     : https://prove2.me/theorems/73e00fda-add3-58a4-bce8-529f27659624
-- title:
--   Finite Field Splitting: ff H fst
-- statement:
--   The Finite Field Splitting construction uses the ff H fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensFFS.lean#L124-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensFFS.lean#L124-L126

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k] {M a : ℕ}

theorem PI.VolStabW.FiniteFieldSplitting.ffH_fst (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).1 = ∑ i, ∑ j, (x i).2 * (J i j).1 * (y j).1 := by sorry
