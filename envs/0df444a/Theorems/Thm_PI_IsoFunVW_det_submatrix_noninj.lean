-- Prove2me | Theorems.Thm_PI_IsoFunVW_det_submatrix_noninj
-- name    : PI.IsoFunVW.det_submatrix_noninj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:10:14.415171+00:00
-- url     : https://prove2.me/theorems/22c85d3f-3b99-40fc-8f54-5adfe1b1c92f
-- title:
--   Iso Fun VW: det submatrix noninj
-- statement:
--   The Iso Fun VW construction uses the det submatrix noninj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/DetSubmatrixNoninj.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/DetSubmatrixNoninj.lean#L27-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_DetSubmatrixNoninj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Equiv
open PI PI.IsoFunVW

theorem PI.IsoFunVW.det_submatrix_noninj {R : Type*} [CommRing R] {m n : ℕ}
    (B : Matrix (Fin n) (Fin m) R) (f : Fin m → Fin n) (hf : ¬ Function.Injective f) :
    (B.submatrix f id).det = 0 := by sorry
