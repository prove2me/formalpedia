-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_liftF_mem
-- name    : PI.UnitaryGroupMassFormula.CntFormula.liftF_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:02.52252+00:00
-- url     : https://prove2.me/theorems/89962195-38bc-4a8b-a521-2e12d0810700
-- title:
--   Cnt Formula: lift F mem
-- statement:
--   The Cnt Formula construction uses the lift F mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/DensGSDvr.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/DensGSDvr.lean#L20-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_DensGSDvr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula
open Classical ValuativeRel
variable (F : Type) [Field F] [ValuativeRel F]

theorem PI.UnitaryGroupMassFormula.CntFormula.liftF_mem (c : 𝓀[F]) : liftF F c ∈ 𝒪[F] := by sorry
