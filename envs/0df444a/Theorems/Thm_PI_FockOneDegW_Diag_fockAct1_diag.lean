-- Prove2me | Theorems.Thm_PI_FockOneDegW_Diag_fockAct1_diag
-- name    : PI.FockOneDegW.Diag.fockAct1_diag
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:31:43.415394+00:00
-- url     : https://prove2.me/theorems/b0efe83a-57f7-5a8f-a237-e6bc3ea09752
-- title:
--   Diag: fock Act1 diag
-- statement:
--   The Diag construction uses the fock Act1 diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/OmEDiagMonomial.lean#L69-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/OmEDiagMonomial.lean#L69-L85

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockOneDegW PI.FockOneDegW.Diag

theorem PI.FockOneDegW.Diag.fockAct1_diag (p q r s : ℕ) (a : Ix p q) :
    fockAct1 p q r s (Eab a a) = ∑ c : Ix r s, omE ((a, c) : Ln p q r s) (a, c) := by sorry
