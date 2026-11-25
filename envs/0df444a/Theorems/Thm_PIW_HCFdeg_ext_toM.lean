-- Prove2me | Theorems.Thm_PIW_HCFdeg_ext_toM
-- name    : PIW.HCFdeg.ext_toM
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:48:35.905387+00:00
-- url     : https://prove2.me/theorems/7ad2a25f-eb8d-5183-9d77-31494f8a2dbc
-- title:
--   HCFdeg: ext to M
-- statement:
--   The HCFdeg construction uses the ext to M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/Unimod.lean#L81-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/Unimod.lean#L81-L81

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Unimod
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
open MeasureTheory PI.UpqRep Matrix
open scoped MatrixOrder NNReal ENNReal ComplexOrder Pointwise
variable {n : ℕ} (ε : Fin n → Bool)

theorem PIW.HCFdeg.ext_toM {a b : UJ ε} (h : toM a = toM b) : a = b := by sorry
