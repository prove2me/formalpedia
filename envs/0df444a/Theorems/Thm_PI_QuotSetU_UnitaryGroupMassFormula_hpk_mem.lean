-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_hpk_mem
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.hpk_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:19:07.499189+00:00
-- url     : https://prove2.me/theorems/40f4cac1-91b5-43e6-92a9-b9aed04188b6
-- title:
--   Unitary Group Mass Formula: hpk mem
-- statement:
--   The Unitary Group Mass Formula construction uses the hpk mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MaximalCompactIsCompact.lean#L133-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MaximalCompactIsCompact.lean#L133-L135

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

theorem PI.QuotSetU.UnitaryGroupMassFormula.hpk_mem (k r : ℕ) : Hpk k r ∈ UH (Hpk k r) := by sorry
