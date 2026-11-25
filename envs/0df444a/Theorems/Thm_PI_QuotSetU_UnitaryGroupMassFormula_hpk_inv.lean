-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_hpk_inv
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.hpk_inv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:19:28.883668+00:00
-- url     : https://prove2.me/theorems/ca346e48-31d0-4d39-a681-82eae654861d
-- title:
--   Unitary Group Mass Formula: hpk inv
-- statement:
--   The Unitary Group Mass Formula construction uses the hpk inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MaximalCompactIsCompact.lean#L99-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MaximalCompactIsCompact.lean#L99-L99

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

theorem PI.QuotSetU.UnitaryGroupMassFormula.hpk_inv (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r := by sorry
