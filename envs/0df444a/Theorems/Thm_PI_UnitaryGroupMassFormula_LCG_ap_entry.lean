-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_entry
-- name    : PI.UnitaryGroupMassFormula.LCG.ap_entry
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:05:26.784843+00:00
-- url     : https://prove2.me/theorems/cea972b3-9ceb-5c78-afc0-15a17f79b320
-- title:
--   LCG: ap entry
-- statement:
--   The LCG construction uses the ap entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L165-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L165-L171

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

theorem PI.UnitaryGroupMassFormula.LCG.ap_entry {n k : ℕ} (Y C : Matrix (Fin n) (Fin k) ℂ) (Jm : Matrix (Fin n) (Fin n) ℂ) (a c : Fin k) :
    (Yᴴ * Jm * C) a c = star (fun i => Y i a) ⬝ᵥ (Jm *ᵥ fun i => C i c) := by sorry
