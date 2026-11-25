-- Prove2me | Theorems.Thm_PI_VolStabS_FiniteFieldSplitting_ffH_snd
-- name    : PI.VolStabS.FiniteFieldSplitting.ffH_snd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:36:04.176658+00:00
-- url     : https://prove2.me/theorems/5279d8a7-6a2a-5057-85b5-8ebdacb5a13b
-- title:
--   Finite Field Splitting: ff H snd
-- statement:
--   The Finite Field Splitting construction uses the ff H snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFS.lean#L132-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFS.lean#L132-L135

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open PI.VolStabS.FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k] {M a : ℕ}

theorem PI.VolStabS.FiniteFieldSplitting.ffH_snd (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).2 = ∑ i, ∑ j, (x i).1 * (J i j).2 * (y j).2 := by sorry
