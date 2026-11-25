-- Prove2me | Theorems.Thm_PI_GGMirBoundW_card_nonzero
-- name    : PI.GGMirBoundW.card_nonzero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:30:34.729992+00:00
-- url     : https://prove2.me/theorems/72139233-3d72-4cb5-b136-94eb70a65542
-- title:
--   GGMir Bound W: card nonzero
-- statement:
--   The GGMir Bound W construction uses the card nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicBound/CardNonzero.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicBound/CardNonzero.lean#L13-L15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_LastRowMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_CardNonzero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGMirBoundW
open Finset Matrix Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical

theorem PI.GGMirBoundW.card_nonzero (F : Type) [Field F] [Fintype F] (m : ℕ) :
    Fintype.card {r : Fin m → F // r ≠ 0} = Fintype.card F ^ m - 1 := by sorry
