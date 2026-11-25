-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_phv_mulVec
-- name    : PI.UnitaryGroupMassFormula.LCG.ap_phv_mulVec
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:39:19.956479+00:00
-- url     : https://prove2.me/theorems/cfafd560-228c-4c4f-a8ec-13b727ca33b9
-- title:
--   LCG: ap phv mul Vec
-- statement:
--   The LCG construction uses the ap phv mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L100-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L100-L103

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

theorem PI.UnitaryGroupMassFormula.LCG.ap_phv_mulVec (v : InfinitePlace I.F) (δ : Matrix (Fin I.n) (Fin I.n) I.E) (w : Fin I.n → I.E) :
    phv I v (δ *ᵥ w) = δ.map (I.φ v) *ᵥ phv I v w := by sorry
