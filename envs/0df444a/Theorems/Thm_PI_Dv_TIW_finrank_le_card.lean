-- Prove2me | Theorems.Thm_PI_Dv_TIW_finrank_le_card
-- name    : PI.Dv.TIW.finrank_le_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:40.880304+00:00
-- url     : https://prove2.me/theorems/7a5ed193-4a9d-4fc2-9bce-2bf81851f0a4
-- title:
--   TIW: finrank le card
-- statement:
--   The TIW construction uses the finrank le card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/AsAlgebraHomMemSpan.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/AsAlgebraHomMemSpan.lean#L43-L47

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
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem PI.Dv.TIW.finrank_le_card (τ : Representation K G W) (hirr : Function.Surjective τ.asAlgebraHom)
    [Nontrivial W] : Module.finrank K W ≤ Fintype.card G := by sorry
