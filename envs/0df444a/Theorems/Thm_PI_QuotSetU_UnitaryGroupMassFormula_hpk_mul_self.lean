-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_hpk_mul_self
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.hpk_mul_self
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:49.353191+00:00
-- url     : https://prove2.me/theorems/77417e94-17ed-4df1-8e5b-66cf58c5e767
-- title:
--   Unitary Group Mass Formula: hpk mul self
-- statement:
--   The Unitary Group Mass Formula construction uses the hpk mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MaximalCompactIsCompact.lean#L61-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MaximalCompactIsCompact.lean#L61-L73

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Mathlib.Analysis.CStarAlgebra.Matrix
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula
open PI PI.QuotSetU

theorem PI.QuotSetU.UnitaryGroupMassFormula.hpk_mul_self (k r : ℕ) : Hpk k r * Hpk k r = 1 := by sorry
