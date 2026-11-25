-- Prove2me | Theorems.Thm_PI_TOW_DegW_multideg_single
-- name    : PI.TOW.DegW.multideg_single
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:28:43.469898+00:00
-- url     : https://prove2.me/theorems/9675ceca-54e2-54c2-933e-2d84bdf6984f
-- title:
--   Deg W: multideg single
-- statement:
--   The Deg W construction uses the multideg single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/MultidegSingle.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/MultidegSingle.lean#L17-L20

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_MultidegSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW PI.TOW.DegW
open PI.TO PI.TOW
variable {K : Type} [Field K] {n' k : ℕ}

theorem PI.TOW.DegW.multideg_single (j : Fin n' × Fin k) (i : Fin n') :
    multideg (Finsupp.single j 1) i = if j.1 = i then 1 else 0 := by sorry
