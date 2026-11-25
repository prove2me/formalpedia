-- Prove2me | Theorems.Thm_PI_MultFromLatWork_const_eq
-- name    : PI.MultFromLatWork.const_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:36:11.290234+00:00
-- url     : https://prove2.me/theorems/fe4695e7-c59e-4267-acbe-6b303c3c668e
-- title:
--   Mult From Lat Work: const eq
-- statement:
--   The Mult From Lat Work construction uses the const eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeMultiplicity/EncardLeOfFinset.lean#L133-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeMultiplicity/EncardLeOfFinset.lean#L133-L141

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatCountG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeMultiplicity_EncardLeOfFinset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ENNReal
noncomputable section
open PI PI.MultFromLatWork
open Formalism.REAL

theorem PI.MultFromLatWork.const_eq (I : Formalism.MainNotions.S.AutInst) (r : NumberField.InfinitePlace I.F → ℝ) (t : ℝ) :
    (3 * Real.sqrt (I.n : ℝ) / (t * t)) ^ (2 * I.n ^ 2 * I.f) *
        Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, (2 * r v)) =
      PI.LatCountG.COm I r / t ^ (4 * I.n ^ 2 * I.f) := by sorry
