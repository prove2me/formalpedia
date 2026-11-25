-- Prove2me | Theorems.Thm_PI_FockOneDegW_RedOps_inner_negOp
-- name    : PI.FockOneDegW.RedOps.inner_negOp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:07:53.967585+00:00
-- url     : https://prove2.me/theorems/15742269-a8ce-4f1a-a455-2f6e47eb1f12
-- title:
--   Red Ops: inner neg Op
-- statement:
--   The Red Ops construction uses the inner neg Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/RedOps.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/RedOps.lean#L59-L68

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockRaiseLow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial FockRaiseLowInner
open PI PI.FockOneDegW PI.FockOneDegW.RedOps
open PI.FockOneDegW
variable {p q r s : ℕ}

theorem PI.FockOneDegW.RedOps.inner_negOp (a b : Ix p q) (hab : sameBlock a b) (P Q : Pol p q r s) :
    fockInner P (negOp a b Q) = fockInner (negOp b a P) Q := by sorry
