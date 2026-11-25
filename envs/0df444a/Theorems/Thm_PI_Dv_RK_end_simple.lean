-- Prove2me | Theorems.Thm_PI_Dv_RK_end_simple
-- name    : PI.Dv.RK.end_simple
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:27:50.649987+00:00
-- url     : https://prove2.me/theorems/9fa19bcb-42f3-4581-b278-2d12607e7b86
-- title:
--   RK: end simple
-- statement:
--   The RK construction uses the end simple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalKernels/AsAlgApply.lean#L33-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalKernels/AsAlgApply.lean#L33-L53

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

theorem PI.Dv.RK.end_simple {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (E : Module.End K W) (hE : E ≠ 0) :
    ∃ (n : ℕ) (A B : Fin n → Module.End K W), ∑ i, A i * E * B i = 1 := by sorry
