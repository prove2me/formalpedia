-- Prove2me | Theorems.Thm_PI_Dv_TIW_eS_mul
-- name    : PI.Dv.TIW.eS_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:27:52.78498+00:00
-- url     : https://prove2.me/theorems/08d88281-0421-43d9-a6d0-561d2524b654
-- title:
--   TIW: e S mul
-- statement:
--   The TIW construction uses the e S mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/TauCentralScalar.lean#L48-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/TauCentralScalar.lean#L48-L62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G) (s : T.S)

theorem PI.Dv.TIW.eS_mul (z : MonoidAlgebra K G) : eS T s * z = theta T s ((T.tau s).asAlgebraHom z) := by sorry
