-- Prove2me | Theorems.Thm_PI_Dv_TIW_li_span_top
-- name    : PI.Dv.TIW.li_span_top
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:56:03.770799+00:00
-- url     : https://prove2.me/theorems/74c488df-be39-4883-87d0-8afa9416bee2
-- title:
--   TIW: li span top
-- statement:
--   The TIW construction uses the li span top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/AsAlgebraHomMemSpan.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/AsAlgebraHomMemSpan.lean#L67-L72

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

theorem PI.Dv.TIW.li_span_top {n : ℕ} (u : Fin n → V) (hu : LinearIndependent K u) (hn : n = Module.finrank K V) :
    Submodule.span K (Set.range u) = ⊤ := by sorry
