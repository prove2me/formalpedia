-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ChooseW_star_li
-- name    : PI.UnitaryGroupMassFormula.LCG.ChooseW.star_li
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:40:28.633333+00:00
-- url     : https://prove2.me/theorems/29349889-c08b-4e79-bd47-6ed2adccf506
-- title:
--   Choose W: star li
-- statement:
--   The Choose W construction uses the star li property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/Choose.lean#L96-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/Choose.lean#L96-L107

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
variable {E : Type*} [Field E] [StarRing E] {n : ℕ}

theorem PI.UnitaryGroupMassFormula.LCG.ChooseW.star_li {k : ℕ} (v : Fin k → Fin n → E) (h : LinearIndependent E v) :
    LinearIndependent E (fun a => sv (v a)) := by sorry
