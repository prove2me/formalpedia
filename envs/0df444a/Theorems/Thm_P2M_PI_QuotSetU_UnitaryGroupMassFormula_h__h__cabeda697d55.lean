-- Prove2me | Theorems.Thm_P2M_PI_QuotSetU_UnitaryGroupMassFormula_h__h__cabeda697d55
-- name    : P2M_PI_QuotSetU_UnitaryGroupMassFormula_h__h__cabeda697d55
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:29.141923+00:00
-- url     : https://prove2.me/theorems/7a652cbf-8052-4122-836c-8e2c4ce14d12
-- title:
--   P2 M PI Quot Set U Unitary Group Mass Formula h  h  cabeda697d55: P2 M PI Quot Set U Unitary Group Mass Formula h  h  cabeda697d55
-- statement:
--   The P2 M PI Quot Set U Unitary Group Mass Formula h  h  cabeda697d55 construction uses the P2 M PI Quot Set U Unitary Group Mass Formula h  h  cabeda697d55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MaximalCompactIsCompact.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MaximalCompactIsCompact.lean#L50-L54

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

theorem P2M_PI_QuotSetU_UnitaryGroupMassFormula_h__h__cabeda697d55 (k r : ℕ) (i : Fin (2 * r + k + 1)) : hσ k r (hσ k r i) = i := by sorry

alias «PI».«QuotSetU».«UnitaryGroupMassFormula».«hσ_hσ» := P2M_PI_QuotSetU_UnitaryGroupMassFormula_h__h__cabeda697d55
