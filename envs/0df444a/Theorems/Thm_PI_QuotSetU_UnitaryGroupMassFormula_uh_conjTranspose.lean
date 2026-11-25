-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_uh_conjTranspose
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.uh_conjTranspose
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:19:16.591994+00:00
-- url     : https://prove2.me/theorems/f9721481-c7e5-43b8-b2fd-8a7e5646e661
-- title:
--   Unitary Group Mass Formula: uh conj Transpose
-- statement:
--   The Unitary Group Mass Formula construction uses the uh conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/GPolar.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/GPolar.lean#L25-L29

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_GPolar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped MatrixOrder ComplexOrder
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula
open PI PI.QuotSetU

theorem PI.QuotSetU.UnitaryGroupMassFormula.uh_conjTranspose {k r : ℕ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : gᴴ ∈ UH (Hpk k r) := by sorry
