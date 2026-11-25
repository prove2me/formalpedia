-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_Dual_den
-- name    : PI.LocFramePrimWork.Dual_den
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:13:06.387364+00:00
-- url     : https://prove2.me/theorems/a917e444-8910-50a5-aeab-4937bef4c042
-- title:
--   Loc Frame Prim Work: Dual den
-- statement:
--   The Loc Frame Prim Work construction uses the Dual den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DualFunctionalsExist.lean#L88-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DualFunctionalsExist.lean#L88-L102

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DualFunctionalsExist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim Module
open scoped TensorProduct
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem PI.LocFramePrimWork.Dual_den {ι : Type} [Fintype ι] (g : ι → Fin n → E) (y : Fin n → E)
    (hy : y ∈ Submodule.span E (Set.range g)) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∃ o : ι → 𝓞 E, (d : E) • y = ∑ i, (o i : E) • g i := by sorry
