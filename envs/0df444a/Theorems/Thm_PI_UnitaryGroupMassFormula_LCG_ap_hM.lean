-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_hM
-- name    : PI.UnitaryGroupMassFormula.LCG.ap_hM
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:48:58.834792+00:00
-- url     : https://prove2.me/theorems/36c66889-8c1a-59e9-aea8-d3c31c393210
-- title:
--   LCG: ap h M
-- statement:
--   The LCG construction uses the ap h M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L194-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L194-L200

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace
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
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.UnitaryGroupMassFormula.LCG.ap_hM (k : ℕ) (b' : Fin k → Fin I.n → I.E) (w : Fin I.n → I.E) (a : Fin k) :
    (hM I b' *ᵥ w) a = hf I (b' a) w := by sorry
