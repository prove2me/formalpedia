-- Prove2me | Theorems.Thm_PI_Dv_Tr_select
-- name    : PI.Dv.Tr.select
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:32:30.557811+00:00
-- url     : https://prove2.me/theorems/a579bbea-82d2-5e1d-8aac-45095da057b8
-- title:
--   Tr: select
-- statement:
--   The Tr construction uses the select property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/PerSAlg.lean#L38-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/PerSAlg.lean#L38-L57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_RankIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_PerSAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module
variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem PI.Dv.Tr.select {ι M : Type} [Fintype ι] [AddCommGroup M] [Module K M] (v : ι → M) (n : ℕ)
    (hn : finrank K (Submodule.span K (Set.range v)) = n) :
    ∃ a : Fin n → ι, LinearIndependent K (v ∘ a) ∧
      Submodule.span K (Set.range (v ∘ a)) = Submodule.span K (Set.range v) := by sorry
