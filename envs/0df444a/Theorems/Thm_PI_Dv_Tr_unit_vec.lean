-- Prove2me | Theorems.Thm_PI_Dv_Tr_unit_vec
-- name    : PI.Dv.Tr.unit_vec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:52.042103+00:00
-- url     : https://prove2.me/theorems/6da444b1-f884-4a3b-8ffb-eb65d80452f5
-- title:
--   Tr: unit vec
-- statement:
--   The Tr construction uses the unit vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/PerSAlg.lean#L59-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/PerSAlg.lean#L59-L69

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

theorem PI.Dv.Tr.unit_vec {n : ℕ} {V : Type} [AddCommGroup V] [Module K V] (N : Matrix (Fin n) (Fin n) K) (hN : IsUnit N)
    (y : Fin n → V) (h : ∀ j, ∑ i, N j i • y i = 0) : y = 0 := by sorry
