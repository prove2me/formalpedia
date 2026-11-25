-- Prove2me | Theorems.Thm_PI_Dv_RK_eG_mem
-- name    : PI.Dv.RK.eG_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:27:42.142406+00:00
-- url     : https://prove2.me/theorems/4f4397a7-9f10-4149-b40a-322303ab1723
-- title:
--   RK: e G mem
-- statement:
--   The RK construction uses the e G mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalKernels/AsAlgApply.lean#L55-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalKernels/AsAlgApply.lean#L55-L72

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

theorem PI.Dv.RK.eG_mem (T : GoodSet K G) (P : Pair K G) (h : ∀ s, (T.tau s).asAlgebraHom (eps P) ≠ 0) :
    eG T ∈ AddSubgroup.closure {w | ∃ a b : MonoidAlgebra K G, w = a * eps P * b} := by sorry
