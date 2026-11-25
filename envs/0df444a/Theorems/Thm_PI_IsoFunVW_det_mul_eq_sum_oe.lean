-- Prove2me | Theorems.Thm_PI_IsoFunVW_det_mul_eq_sum_oe
-- name    : PI.IsoFunVW.det_mul_eq_sum_oe
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:09:57.551827+00:00
-- url     : https://prove2.me/theorems/c698b33b-d0eb-403e-9bd3-55d439b3729c
-- title:
--   Iso Fun VW: det mul eq sum oe
-- statement:
--   The Iso Fun VW construction uses the det mul eq sum oe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/DetSubmatrixNoninj.lean#L34-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/DetSubmatrixNoninj.lean#L34-L99

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

theorem PI.IsoFunVW.det_mul_eq_sum_oe {R : Type*} [CommRing R] {m n : ℕ} [Fintype (Fin m ↪o Fin n)]
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det = ∑ J : Fin m ↪o Fin n, (A.submatrix id J).det * (B.submatrix J id).det := by sorry
