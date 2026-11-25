-- Prove2me | Theorems.Thm_PI_VolStabSW_FiniteFieldSplitting_ffH_snd
-- name    : PI.VolStabSW.FiniteFieldSplitting.ffH_snd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:41:47.051667+00:00
-- url     : https://prove2.me/theorems/33a87aab-fc07-41c6-8ef1-3b7ba19e3df5
-- title:
--   Finite Field Splitting: ff H snd
-- statement:
--   The Finite Field Splitting construction uses the ff H snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensFFS.lean#L132-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensFFS.lean#L132-L135

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k] {M a : ℕ}

theorem PI.VolStabSW.FiniteFieldSplitting.ffH_snd (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).2 = ∑ i, ∑ j, (x i).1 * (J i j).2 * (y j).2 := by sorry
