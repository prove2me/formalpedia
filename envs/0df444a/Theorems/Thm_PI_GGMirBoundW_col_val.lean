-- Prove2me | Theorems.Thm_PI_GGMirBoundW_col_val
-- name    : PI.GGMirBoundW.col_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:23.701524+00:00
-- url     : https://prove2.me/theorems/8042bafb-900e-49d9-9a1d-c8e78f240476
-- title:
--   GGMir Bound W: col val
-- statement:
--   The GGMir Bound W construction uses the col val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicBound/LastRowMul.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicBound/LastRowMul.lean#L51-L52

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
variable {F : Type} [Field F] [Fintype F] {n : ℕ}

theorem PI.GGMirBoundW.col_val (x : Fin n → F) : ((col x : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
    colM x := by sorry
