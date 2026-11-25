-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_rFrame_of
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.rFrame_of
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:00:18.047633+00:00
-- url     : https://prove2.me/theorems/5b1e13d2-3735-4688-98c9-6c213e353508
-- title:
--   Unitary Group Mass Formula: r Frame of
-- statement:
--   The Unitary Group Mass Formula construction uses the r Frame of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousHPart.lean#L22-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousHPart.lean#L22-L33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousHPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable {n r : ℕ} (ε : Fin n → Bool)

theorem PI.ScMuExists.UnitaryGroupMassFormula.rFrame_of {I : Formalism.MainNotions.S.AutInst} {r : ℕ} {e f : Fin r → Fin I.n → I.E} {z : Fin I.n → I.E}
    (hF : IsFrame I e f z) (v : NumberField.InfinitePlace I.F) :
    RFrame (I.ε v) (fun a => rv I v (e a)) (fun a => rv I v (f a)) (rv I v z) := by sorry
