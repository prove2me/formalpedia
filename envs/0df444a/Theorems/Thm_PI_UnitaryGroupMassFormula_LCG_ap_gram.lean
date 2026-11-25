-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_gram
-- name    : PI.UnitaryGroupMassFormula.LCG.ap_gram
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:46:38.946133+00:00
-- url     : https://prove2.me/theorems/2e13a1cd-d1a2-5800-a03f-c6eaa94950bc
-- title:
--   LCG: ap gram
-- statement:
--   The LCG construction uses the ap gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L116-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L116-L119

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

theorem PI.UnitaryGroupMassFormula.LCG.ap_gram (z : I.GA) (v : InfinitePlace I.F) {k : ℕ} (b : Fin k → Fin I.n → I.E) :
    PI.LatCountG.gramV I z v b = (colM I z v b)ᴴ * colM I z v b := by sorry
