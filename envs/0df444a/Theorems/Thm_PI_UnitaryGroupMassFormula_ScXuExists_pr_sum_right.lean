-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_pr_sum_right
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.pr_sum_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:39:55.743244+00:00
-- url     : https://prove2.me/theorems/5b3c2ea2-9414-5940-ac38-10306b788e53
-- title:
--   Sc Xu Exists: pr sum right
-- statement:
--   The Sc Xu Exists construction uses the pr sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LinBase.lean#L49-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LinBase.lean#L49-L55

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

theorem PI.UnitaryGroupMassFormula.ScXuExists.pr_sum_right {ι : Type} (s : Finset ι) (β : Fin n → K) (x : ι → Fin n → K) :
    pr P β (∑ i ∈ s, x i) = ∑ i ∈ s, pr P β (x i) := by sorry
