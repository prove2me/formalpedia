-- Prove2me | Theorems.Thm_PIW_HCFdeg_isCompact_KG
-- name    : PIW.HCFdeg.isCompact_KG
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:56:04.599864+00:00
-- url     : https://prove2.me/theorems/ebd1a323-ea65-460d-9f85-34ab9a3781dd
-- title:
--   HCFdeg: is Compact KG
-- statement:
--   The HCFdeg construction uses the is Compact KG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/Unimod.lean#L157-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/Unimod.lean#L157-L158

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

theorem PIW.HCFdeg.isCompact_KG : IsCompact ((KG ε : Set (UJ ε))) := by sorry
