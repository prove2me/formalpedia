-- Prove2me | Theorems.Thm_PI_GGMirBoundW_lastRow_mul
-- name    : PI.GGMirBoundW.lastRow_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:31:15.522737+00:00
-- url     : https://prove2.me/theorems/4c932e88-5b14-4e29-ba97-4e1488584fd4
-- title:
--   GGMir Bound W: last Row mul
-- statement:
--   The GGMir Bound W construction uses the last Row mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicBound/LastRowMul.lean#L152-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicBound/LastRowMul.lean#L152-L158

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_LastRowMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGMirBoundW
open Matrix Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical

theorem PI.GGMirBoundW.lastRow_mul {F : Type} [Field F] [Fintype F] {n : ℕ} {p : GL (Fin (n + 1)) F} (hp : LastRowE p)
    (g : GL (Fin (n + 1)) F) (j : Fin (n + 1)) :
    ((p * g : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j =
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j := by sorry
