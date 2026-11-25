-- Prove2me | Theorems.Thm_PI_Dv_RK_tau_eps_ne
-- name    : PI.Dv.RK.tau_eps_ne
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:30:10.960407+00:00
-- url     : https://prove2.me/theorems/57e60577-d590-5c30-b3b5-9d3e7c8afaca
-- title:
--   RK: tau eps ne
-- statement:
--   The RK construction uses the tau eps ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalKernels/AsAlgApply.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalKernels/AsAlgApply.lean#L74-L80

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_AsAlgApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.RK
open MonoidAlgebra
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.RK.tau_eps_ne (T : GoodSet K G) (P : Pair K G) (h : M1 T P) (s : T.S) :
    (T.tau s).asAlgebraHom (eps P) ≠ 0 := by sorry
