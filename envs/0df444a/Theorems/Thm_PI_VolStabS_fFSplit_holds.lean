-- Prove2me | Theorems.Thm_PI_VolStabS_fFSplit_holds
-- name    : PI.VolStabS.fFSplit_holds
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:36:24.459855+00:00
-- url     : https://prove2.me/theorems/72df234e-ef71-5f22-a292-85326b4664b8
-- title:
--   Vol Stab S: f FSplit holds
-- statement:
--   The Vol Stab S construction uses the f FSplit holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFS.lean#L233-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFS.lean#L233-L243

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

theorem PI.VolStabS.fFSplit_holds : FFSplit := by sorry
