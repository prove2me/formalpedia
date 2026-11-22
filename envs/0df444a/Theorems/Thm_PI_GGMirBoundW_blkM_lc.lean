-- Prove2me | Theorems.Thm_PI_GGMirBoundW_blkM_lc
-- name    : PI.GGMirBoundW.blkM_lc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:01.452805+00:00
-- url     : https://prove2.me/theorems/0176a734-4d37-447b-a844-6d2a2e6c55b7
-- title:
--   GGMir Bound W: blk M lc
-- statement:
--   The GGMir Bound W construction uses the blk M lc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicBound/LastRowMul.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicBound/LastRowMul.lean#L24-L26

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

theorem PI.GGMirBoundW.blkM_lc (A : Matrix (Fin n) (Fin n) F) (j : Fin n) :
    blkM A (Fin.last n) (Fin.castSucc j) = 0 := by sorry
