-- Prove2me | Theorems.Thm_PI_Dv_TIW_mul_eS
-- name    : PI.Dv.TIW.mul_eS
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:21.273768+00:00
-- url     : https://prove2.me/theorems/c690146b-4446-4228-b490-c8be7451aa07
-- title:
--   TIW: mul e S
-- statement:
--   The TIW construction uses the mul e S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/TauCentralScalar.lean#L35-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/TauCentralScalar.lean#L35-L46

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

theorem PI.Dv.TIW.mul_eS (z : MonoidAlgebra K G) : z * eS T s = theta T s ((T.tau s).asAlgebraHom z) := by sorry
