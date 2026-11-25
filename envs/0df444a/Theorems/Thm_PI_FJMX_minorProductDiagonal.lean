-- Prove2me | Theorems.Thm_PI_FJMX_minorProductDiagonal
-- name    : PI.FJMX.minorProductDiagonal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:30:38.119541+00:00
-- url     : https://prove2.me/theorems/c1c0a3f7-9d1d-5581-b627-95514f114f8d
-- title:
--   FJMX: minor Product Diagonal
-- statement:
--   The FJMX construction uses the minor Product Diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/CauBFin.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/CauBFin.lean#L6-L7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurCauchy
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauBFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FJMX

theorem PI.FJMX.minorProductDiagonal : PI.FJMB.HypShape := by sorry
