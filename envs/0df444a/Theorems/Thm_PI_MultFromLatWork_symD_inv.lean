-- Prove2me | Theorems.Thm_PI_MultFromLatWork_symD_inv
-- name    : PI.MultFromLatWork.symD_inv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:35:59.854522+00:00
-- url     : https://prove2.me/theorems/1334b8e5-8ae6-45d3-ade3-d7e330ab5249
-- title:
--   Mult From Lat Work: sym D inv
-- statement:
--   The Mult From Lat Work construction uses the sym D inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeMultiplicity/EncardLeOfFinset.lean#L109-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeMultiplicity/EncardLeOfFinset.lean#L109-L114

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

theorem PI.MultFromLatWork.symD_inv {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : PI.symD ε g⁻¹ = PI.symD ε g := by sorry
