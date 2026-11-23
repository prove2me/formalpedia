-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_one_add_smul_vecMulVec_mulVec
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.one_add_smul_vecMulVec_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:42.838043+00:00
-- url     : https://prove2.me/theorems/d4ccf5b9-7a6e-41cc-a3d9-ee8edc418b42
-- title:
--   Sc Xu Exists: one add smul vec Mul Vec mul Vec
-- statement:
--   The Sc Xu Exists construction uses the one add smul vec Mul Vec mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LinBase.lean#L93-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LinBase.lean#L93-L99

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

theorem PI.UnitaryGroupMassFormula.ScXuExists.one_add_smul_vecMulVec_mulVec (p q x : Fin n → R) (c : R) :
    (1 + c • vecMulVec p q) *ᵥ x = x + (c * (q ⬝ᵥ x)) • p := by sorry
