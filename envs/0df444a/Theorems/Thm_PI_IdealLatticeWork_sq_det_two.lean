-- Prove2me | Theorems.Thm_PI_IdealLatticeWork_sq_det_two
-- name    : PI.IdealLatticeWork.sq_det_two
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:18.994773+00:00
-- url     : https://prove2.me/theorems/bdb03cfb-3e5f-4604-bff0-e5fba947a630
-- title:
--   Ideal Lattice Work: sq det two
-- statement:
--   The Ideal Lattice Work construction uses the sq det two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdealLatticeBasis/OKArea.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdealLatticeBasis/OKArea.lean#L8-L11

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdealLatticeBasis_IdealBasisAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdealLatticeBasis_OKArea
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.IdealLatticeWork

theorem PI.IdealLatticeWork.sq_det_two (x y : ℂ) :
    (x * (starRingEnd ℂ) y - (starRingEnd ℂ) x * y) ^ 2
      = (((-4) * (((starRingEnd ℂ) x * y).im) ^ 2 : ℝ) : ℂ) := by sorry
