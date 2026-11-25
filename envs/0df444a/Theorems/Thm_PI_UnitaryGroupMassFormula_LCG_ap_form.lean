-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_form
-- name    : PI.UnitaryGroupMassFormula.LCG.ap_form
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:40:57.244011+00:00
-- url     : https://prove2.me/theorems/bba540ff-41a9-474b-abc9-1cfadbf5c957
-- title:
--   LCG: ap form
-- statement:
--   The LCG construction uses the ap form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L157-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L157-L163

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

theorem PI.UnitaryGroupMassFormula.LCG.ap_form (v : InfinitePlace I.F) (w z : Fin I.n → I.E) :
    I.φ v (hf I w z) = star (phv I v w) ⬝ᵥ (I.J.map (I.φ v) *ᵥ phv I v z) := by sorry
