-- Prove2me | Theorems.Thm_PIW_HCFdeg_stOrthOf
-- name    : PIW.HCFdeg.stOrthOf
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:47:21.440054+00:00
-- url     : https://prove2.me/theorems/7a70442d-a5b9-490a-8a93-dd0b845445a9
-- title:
--   HCFdeg: st Orth Of
-- statement:
--   The HCFdeg construction uses the st Orth Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/IntegrableCf.lean#L48-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/IntegrableCf.lean#L48-L146

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_IntegrableCf
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
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

theorem PIW.HCFdeg.stOrthOf : StOrthOf := by sorry
