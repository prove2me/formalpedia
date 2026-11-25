-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ChooseW_rank_pos
-- name    : PI.UnitaryGroupMassFormula.LCG.ChooseW.rank_pos
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:49:51.779104+00:00
-- url     : https://prove2.me/theorems/e8e930fa-e0af-5dfd-b39e-1317c19bb7f7
-- title:
--   Choose W: rank pos
-- statement:
--   The Choose W construction uses the rank pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/Choose.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/Choose.lean#L76-L83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_Choose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.ChooseW
variable {K : Type*} [Field K] {n : ℕ}

theorem PI.UnitaryGroupMassFormula.LCG.ChooseW.rank_pos (δ : Matrix (Fin n) (Fin n) K) (hδ : δ ≠ 0) : 1 ≤ δ.rank := by sorry
