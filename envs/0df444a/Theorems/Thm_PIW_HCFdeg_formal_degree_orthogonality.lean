-- Prove2me | Theorems.Thm_PIW_HCFdeg_formal_degree_orthogonality
-- name    : PIW.HCFdeg.formal_degree_orthogonality
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:49:42.102592+00:00
-- url     : https://prove2.me/theorems/ebc500be-9792-491a-b2dd-d069beec9bf5
-- title:
--   HCFdeg: formal degree orthogonality
-- statement:
--   The HCFdeg construction uses the formal degree orthogonality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/FormalDegreeOrthogonality.lean#L29-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/FormalDegreeOrthogonality.lean#L29-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeOrthogonality
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
open MeasureTheory PI.UpqRep
open scoped InnerProductSpace

theorem PIW.HCFdeg.formal_degree_orthogonality : FormalDegreeFromOrthogonality := by sorry
