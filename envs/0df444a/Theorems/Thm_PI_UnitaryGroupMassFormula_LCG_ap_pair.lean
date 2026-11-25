-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_pair
-- name    : PI.UnitaryGroupMassFormula.LCG.ap_pair
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:40:16.614556+00:00
-- url     : https://prove2.me/theorems/00b90133-ee89-407a-8655-4b88120fa01f
-- title:
--   LCG: ap pair
-- statement:
--   The LCG construction uses the ap pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L147-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L147-L150

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

theorem PI.UnitaryGroupMassFormula.LCG.ap_pair (y : I.GA) (v : InfinitePlace I.F) (p q : Fin I.n → ℂ) :
    star (qM I y v *ᵥ p) ⬝ᵥ (Formalism.REAL.Jm (I.ε v) *ᵥ (qM I y v *ᵥ q)) =
      star p ⬝ᵥ (I.J.map (I.φ v) *ᵥ q) := by sorry
