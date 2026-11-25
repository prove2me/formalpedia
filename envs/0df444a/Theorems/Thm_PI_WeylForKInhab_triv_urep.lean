-- Prove2me | Theorems.Thm_PI_WeylForKInhab_triv_urep
-- name    : PI.WeylForKInhab.triv_urep
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:48:57.487803+00:00
-- url     : https://prove2.me/theorems/16a417fa-9e3f-4a32-934a-257df19e379e
-- title:
--   Weyl For KInhab: triv urep
-- statement:
--   The Weyl For KInhab construction uses the triv urep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/TrivKtype.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/TrivKtype.lean#L31-L34

import Definitions.Def_Formalism_PeriodIntegrals_WeylForK
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_TrivKtype
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UpqRep Matrix
noncomputable section
open PI PI.WeylForKInhab

theorem PI.WeylForKInhab.triv_urep {N : ℕ} (ε : Fin N → Bool) : IsURepOn (Kset ε) (triv N) := by sorry
