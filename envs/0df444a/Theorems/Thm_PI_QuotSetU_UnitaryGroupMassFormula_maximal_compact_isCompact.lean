-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_maximal_compact_isCompact
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.maximal_compact_isCompact
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:29:42.58799+00:00
-- url     : https://prove2.me/theorems/1cdccaa9-25b6-4547-8ad6-0dd105fa0efb
-- title:
--   Unitary Group Mass Formula: maximal compact is Compact
-- statement:
--   The Unitary Group Mass Formula construction uses the maximal compact is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MaximalCompactIsCompact.lean#L162-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MaximalCompactIsCompact.lean#L162-L177

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

theorem PI.QuotSetU.UnitaryGroupMassFormula.maximal_compact_isCompact : KCompact := by sorry
