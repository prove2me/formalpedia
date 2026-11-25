-- Prove2me | Theorems.Thm_P2M_PI_QuotSetU_UnitaryGroupMassFormula_h__eq_iff_acb49a50f83f
-- name    : P2M_PI_QuotSetU_UnitaryGroupMassFormula_h__eq_iff_acb49a50f83f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:57:35.649087+00:00
-- url     : https://prove2.me/theorems/231110ff-1f03-45a1-8f03-7336a766fb46
-- title:
--   P2 M PI Quot Set U Unitary Group Mass Formula h  eq iff acb49a50f83f: P2 M PI Quot Set U Unitary Group Mass Formula h  eq iff acb49a50f83f
-- statement:
--   The P2 M PI Quot Set U Unitary Group Mass Formula h  eq iff acb49a50f83f construction uses the P2 M PI Quot Set U Unitary Group Mass Formula h  eq iff acb49a50f83f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MaximalCompactIsCompact.lean#L84-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MaximalCompactIsCompact.lean#L84-L89

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

theorem P2M_PI_QuotSetU_UnitaryGroupMassFormula_h__eq_iff_acb49a50f83f (k r : ℕ) (i j : Fin (2 * r + k + 1)) : i = hσ k r j ↔ j = hσ k r i := by sorry

alias «PI».«QuotSetU».«UnitaryGroupMassFormula».«hσ_eq_iff» := P2M_PI_QuotSetU_UnitaryGroupMassFormula_h__eq_iff_acb49a50f83f
