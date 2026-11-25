-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_hpk_conjTranspose
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.hpk_conjTranspose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:45.096768+00:00
-- url     : https://prove2.me/theorems/67e753d4-cc4e-4c1c-934b-1cd0f822b1fe
-- title:
--   Unitary Group Mass Formula: hpk conj Transpose
-- statement:
--   The Unitary Group Mass Formula construction uses the hpk conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MaximalCompactIsCompact.lean#L91-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MaximalCompactIsCompact.lean#L91-L97

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

theorem PI.QuotSetU.UnitaryGroupMassFormula.hpk_conjTranspose (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by sorry
