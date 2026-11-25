-- Prove2me | Theorems.Thm_PI_Dv_TIW_dual_span
-- name    : PI.Dv.TIW.dual_span
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:28:37.405153+00:00
-- url     : https://prove2.me/theorems/5d18ba83-a89c-4965-9c1f-d4229cde2860
-- title:
--   TIW: dual span
-- statement:
--   The TIW construction uses the dual span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/AsAlgebraHomMemSpan.lean#L74-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/AsAlgebraHomMemSpan.lean#L74-L88

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan
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
variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem PI.Dv.TIW.dual_span {ι : Type} (ψ : ι → Module.Dual K V) (h : ∀ v, (∀ i, ψ i v = 0) → v = 0) :
    Submodule.span K (Set.range ψ) = ⊤ := by sorry
