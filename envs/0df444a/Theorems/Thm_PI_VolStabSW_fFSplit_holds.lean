-- Prove2me | Theorems.Thm_PI_VolStabSW_fFSplit_holds
-- name    : PI.VolStabSW.fFSplit_holds
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:42:26.187826+00:00
-- url     : https://prove2.me/theorems/83104303-5672-4045-aff0-f3529218f2b4
-- title:
--   Vol Stab SW: f FSplit holds
-- statement:
--   The Vol Stab SW construction uses the f FSplit holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensFFS.lean#L233-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensFFS.lean#L233-L243

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

theorem PI.VolStabSW.fFSplit_holds : FFSplit := by sorry
