-- Prove2me | Theorems.Thm_PIW_HCFdeg_inUJ_mul_J_conj
-- name    : PIW.HCFdeg.inUJ_mul_J_conj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:16.669453+00:00
-- url     : https://prove2.me/theorems/f6cc2aa2-2204-45e8-b801-d998c32b46d0
-- title:
--   HCFdeg: in UJ mul J conj
-- statement:
--   The HCFdeg construction uses the in UJ mul J conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/Unimod.lean#L103-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/Unimod.lean#L103-L107

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

theorem PIW.HCFdeg.inUJ_mul_J_conj {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : g * Jm ε * gᴴ = Jm ε := by sorry
