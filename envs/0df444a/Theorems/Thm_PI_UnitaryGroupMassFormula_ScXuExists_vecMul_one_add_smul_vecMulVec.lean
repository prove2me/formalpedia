-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_vecMul_one_add_smul_vecMulVec
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.vecMul_one_add_smul_vecMulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:04.682047+00:00
-- url     : https://prove2.me/theorems/e1de6db7-5019-4681-97e2-a520b0731fe0
-- title:
--   Sc Xu Exists: vec Mul one add smul vec Mul Vec
-- statement:
--   The Sc Xu Exists construction uses the vec Mul one add smul vec Mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LinBase.lean#L101-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LinBase.lean#L101-L107

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open Matrix
variable {R : Type} [CommRing R] {n : ℕ}

theorem PI.UnitaryGroupMassFormula.ScXuExists.vecMul_one_add_smul_vecMulVec (p q y : Fin n → R) (c : R) :
    y ᵥ* (1 + c • vecMulVec p q) = y + (c * (y ⬝ᵥ p)) • q := by sorry
