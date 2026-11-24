-- Prove2me | Theorems.Thm_PI_FockWtDegWork_abs_le_of
-- name    : PI.FockWtDegWork.abs_le_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:21.219155+00:00
-- url     : https://prove2.me/theorems/6de119f3-37d3-42ee-8e34-8afa90cd036c
-- title:
--   Fock Wt Deg Work: abs le of
-- statement:
--   The Fock Wt Deg Work construction uses the abs le of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L212-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L212-L214

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockWtDegWork

theorem PI.FockWtDegWork.abs_le_of (x A B : ℚ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : x = A - B) : |x| ≤ A + B := by sorry
