-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_pr_smul_right
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.pr_smul_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:40:12.364802+00:00
-- url     : https://prove2.me/theorems/989ef9a2-2144-4e29-88b1-2fd4034f6c0c
-- title:
--   Sc Xu Exists: pr smul right
-- statement:
--   The Sc Xu Exists construction uses the pr smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LinBase.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LinBase.lean#L37-L39

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

theorem PI.UnitaryGroupMassFormula.ScXuExists.pr_smul_right (c : K) (β x : Fin n → K) : pr P β (c • x) = c * pr P β x := by sorry
