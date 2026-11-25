-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ChooseW_hf_eq
-- name    : PI.UnitaryGroupMassFormula.LCG.ChooseW.hf_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:41:26.392049+00:00
-- url     : https://prove2.me/theorems/ad75b72a-13eb-4253-aaa7-a648babeb2c5
-- title:
--   Choose W: hf eq
-- statement:
--   The Choose W construction uses the hf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/Choose.lean#L138-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/Choose.lean#L138-L140

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

theorem PI.UnitaryGroupMassFormula.LCG.ChooseW.hf_eq (I : Formalism.MainNotions.S.AutInst) (w z : Fin I.n → I.E) : hf I w z = (sv w ᵥ* I.J) ⬝ᵥ z := by sorry
