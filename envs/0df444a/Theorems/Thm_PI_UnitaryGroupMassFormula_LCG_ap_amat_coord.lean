-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_amat_coord
-- name    : PI.UnitaryGroupMassFormula.LCG.ap_amat_coord
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:46:20.910593+00:00
-- url     : https://prove2.me/theorems/2b9dd2db-4c2e-5a40-89b0-9c11eeaf8411
-- title:
--   LCG: ap amat coord
-- statement:
--   The LCG construction uses the ap amat coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L111-L114

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

theorem PI.UnitaryGroupMassFormula.LCG.ap_amat_coord (x y : I.GA) (v : InfinitePlace I.F) (δ : Matrix (Fin I.n) (Fin I.n) I.E)
    (w : Fin I.n → I.E) :
    amat I x y v δ *ᵥ PI.LatCountG.coordV I y v w = PI.LatCountG.coordV I x v (δ *ᵥ w) := by sorry
