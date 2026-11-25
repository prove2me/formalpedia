-- Prove2me | Theorems.Thm_P2M_PI_QuotSetU_UnitaryGroupMassFormula_hs_h__621b40982ce1
-- name    : P2M_PI_QuotSetU_UnitaryGroupMassFormula_hs_h__621b40982ce1
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:57:17.84953+00:00
-- url     : https://prove2.me/theorems/4eb157a7-7949-5a7a-8991-8ec75d179ed9
-- title:
--   P2 M PI Quot Set U Unitary Group Mass Formula hs h  621b40982ce1: P2 M PI Quot Set U Unitary Group Mass Formula hs h  621b40982ce1
-- statement:
--   The P2 M PI Quot Set U Unitary Group Mass Formula hs h  621b40982ce1 construction uses the P2 M PI Quot Set U Unitary Group Mass Formula hs h  621b40982ce1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MaximalCompactIsCompact.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MaximalCompactIsCompact.lean#L75-L78

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

theorem P2M_PI_QuotSetU_UnitaryGroupMassFormula_hs_h__621b40982ce1 (k r : ℕ) (i : Fin (2 * r + k + 1)) : hs k r (hσ k r i) = hs k r i := by sorry

alias «PI».«QuotSetU».«UnitaryGroupMassFormula».«hs_hσ» := P2M_PI_QuotSetU_UnitaryGroupMassFormula_hs_h__621b40982ce1
