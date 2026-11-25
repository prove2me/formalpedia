-- Prove2me | Theorems.Thm_PI_KerIso_FourSqW_main
-- name    : PI.KerIso.FourSqW.main
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:34:16.059446+00:00
-- url     : https://prove2.me/theorems/966a7760-9194-40fb-9dbc-c758ff7bf6ce
-- title:
--   Four Sq W: main
-- statement:
--   The Four Sq W construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/FourSqOfFromDiag.lean#L6-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/FourSqOfFromDiag.lean#L6-L6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_OrthogonalDiagonal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QmapInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOfFromDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.KerIso PI.KerIso.FourSqW

theorem PI.KerIso.FourSqW.main : FourSq := by sorry
