-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_evI_diag
-- name    : PI.AlgValsFin.W.evI_diag
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:23:18.09614+00:00
-- url     : https://prove2.me/theorems/81bb07a3-b080-40b3-ba1a-ccc42154ce79
-- title:
--   W: ev I diag
-- statement:
--   The W construction uses the ev I diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/EvFLocalIdeleSelf.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/EvFLocalIdeleSelf.lean#L29-L30

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ValuedAtFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]

theorem PI.AlgValsFin.W.evI_diag (w : InfinitePlace L) (k : Lˣ) : evI w (diagUnits L k) = atInf w k := by sorry
