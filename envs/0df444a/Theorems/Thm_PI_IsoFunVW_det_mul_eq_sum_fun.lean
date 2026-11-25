-- Prove2me | Theorems.Thm_PI_IsoFunVW_det_mul_eq_sum_fun
-- name    : PI.IsoFunVW.det_mul_eq_sum_fun
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:10:20.360843+00:00
-- url     : https://prove2.me/theorems/6a4420fd-d153-4c4e-8962-20cc40fd5e20
-- title:
--   Iso Fun VW: det mul eq sum fun
-- statement:
--   The Iso Fun VW construction uses the det mul eq sum fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/DetSubmatrixNoninj.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/DetSubmatrixNoninj.lean#L11-L25

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

theorem PI.IsoFunVW.det_mul_eq_sum_fun {R : Type*} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det = ∑ f : Fin m → Fin n, (∏ i, A i (f i)) * (B.submatrix f id).det := by sorry
