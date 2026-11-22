-- Prove2me | Theorems.Thm_PI_GGMirBoundW_blkM_cl
-- name    : PI.GGMirBoundW.blkM_cl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:10.834671+00:00
-- url     : https://prove2.me/theorems/d62511cc-31e7-424d-a43d-21c32ab00fd6
-- title:
--   GGMir Bound W: blk M cl
-- statement:
--   The GGMir Bound W construction uses the blk M cl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicBound/LastRowMul.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicBound/LastRowMul.lean#L20-L22

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

theorem PI.GGMirBoundW.blkM_cl (A : Matrix (Fin n) (Fin n) F) (i : Fin n) :
    blkM A (Fin.castSucc i) (Fin.last n) = 0 := by sorry
