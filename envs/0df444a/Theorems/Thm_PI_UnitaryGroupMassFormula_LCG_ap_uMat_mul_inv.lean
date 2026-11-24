-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_uMat_mul_inv
-- name    : PI.UnitaryGroupMassFormula.LCG.ap_uMat_mul_inv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:51:50.507707+00:00
-- url     : https://prove2.me/theorems/a721f9ea-3a82-4765-a9b7-18cd3fa90917
-- title:
--   LCG: ap u Mat mul inv
-- statement:
--   The LCG construction uses the ap u Mat mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L52-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L52-L58

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

theorem PI.UnitaryGroupMassFormula.LCG.ap_uMat_mul_inv {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ = 1 := by sorry
