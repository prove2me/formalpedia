-- Prove2me | Theorems.Thm_PI_KerFourSqW_quat_herm
-- name    : PI.KerFourSqW.quat_herm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:33:02.582694+00:00
-- url     : https://prove2.me/theorems/fd9da75c-2d65-57a1-8744-6a644e193b3e
-- title:
--   Ker Four Sq W: quat herm
-- statement:
--   The Ker Four Sq W construction uses the quat herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/QuatMatTransposeMul.lean#L51-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/QuatMatTransposeMul.lean#L51-L70

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QuatMatTransposeMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open PI PI.KerFourSqW

theorem PI.KerFourSqW.quat_herm {L F : Type*} [Field L] [CharZero L] [FunLike F L L] [RingHomClass F L L] (c : F) (Q : Matrix (Fin 4) (Fin 4) ℚ) (a : ℚ)
    (hQ : Qᵀ * Q = a • (1 : Matrix (Fin 4) (Fin 4) ℚ)) (x y : Fin 4 → L) :
    ∑ b, (∑ j, (Q b j : L) * x j) * c (∑ k, (Q b k : L) * y k) = (a : L) * ∑ j, x j * c (y j) := by sorry
