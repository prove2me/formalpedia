-- Prove2me | Theorems.Thm_PI_VolStabS_FFHS_ffH_single
-- name    : PI.VolStabS.FFHS.ffH_single
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:37:04.891335+00:00
-- url     : https://prove2.me/theorems/6eece617-858f-5ec6-b1cd-5f64ec5ee7cc
-- title:
--   FFHS: ff H single
-- statement:
--   The FFHS construction uses the ff H single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFIn.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFIn.lean#L47-L52

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFCnt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFIn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.FFHS
open Module Polynomial
variable {K : Type} [Field K] {σ : K →+* K}

theorem PI.VolStabS.FFHS.ffH_single {n : ℕ} (T : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    ffH σ T (Pi.single i 1) (Pi.single j 1) = T i j := by sorry
