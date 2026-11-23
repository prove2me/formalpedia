-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_pr_smul_left
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.pr_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:46.200382+00:00
-- url     : https://prove2.me/theorems/9c5ffafc-7e20-480f-b0d0-e0ecd284bc8c
-- title:
--   Sc Xu Exists: pr smul left
-- statement:
--   The Sc Xu Exists construction uses the pr smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LinBase.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LinBase.lean#L24-L27

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
variable {K : Type} [Field K] {n : ℕ} (P : Matrix (Fin n) (Fin n) K)

theorem PI.UnitaryGroupMassFormula.ScXuExists.pr_smul_left (c : K) (β x : Fin n → K) : pr P (c • β) x = c * pr P β x := by sorry
