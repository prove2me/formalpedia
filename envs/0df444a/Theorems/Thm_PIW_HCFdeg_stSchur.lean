-- Prove2me | Theorems.Thm_PIW_HCFdeg_stSchur
-- name    : PIW.HCFdeg.stSchur
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:47:16.468581+00:00
-- url     : https://prove2.me/theorems/62b9b95f-b9b8-5f0b-84d1-4ce4d337b1d1
-- title:
--   HCFdeg: st Schur
-- statement:
--   The HCFdeg construction uses the st Schur property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/CommuteStar.lean#L128-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/CommuteStar.lean#L128-L145

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_CommuteStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open scoped InnerProductSpace ComplexStarModule
open ContinuousLinearMap

theorem PIW.HCFdeg.stSchur : StSchur := by sorry
