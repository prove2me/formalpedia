-- Prove2me | Theorems.Thm_PI_FGTFG_nzsd_sub
-- name    : PI.FGTFG.nzsd_sub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:49.364555+00:00
-- url     : https://prove2.me/theorems/5689d6a7-294f-52aa-b691-98e36bc4d8a0
-- title:
--   FGTFG: nzsd sub
-- statement:
--   The FGTFG construction uses the nzsd sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorsionFreeGenerators/FGTorsionFreeGenOf.lean#L7-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorsionFreeGenerators/FGTorsionFreeGenOf.lean#L7-L9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorsionFreeGenerators_RankOneStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorsionFreeGenerators_FGTorsionFreeGenOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FGTFG
open Module

theorem PI.FGTFG.nzsd_sub {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [NoZeroSMulDivisors R M] (N : Submodule R M) : NoZeroSMulDivisors R N := by sorry
