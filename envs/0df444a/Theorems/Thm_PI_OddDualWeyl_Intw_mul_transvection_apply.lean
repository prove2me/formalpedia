-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Intw_mul_transvection_apply
-- name    : PI.OddDualWeyl.Intw.mul_transvection_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:14:21.738716+00:00
-- url     : https://prove2.me/theorems/9e8381f8-f413-4507-965f-ca8b58b90a49
-- title:
--   Intw: mul transvection apply
-- statement:
--   The Intw construction uses the mul transvection apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/TransvectionMulApply.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/TransvectionMulApply.lean#L23-L29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_TransvectionMulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open PI.OddDualWeyl.Intw
variable {A : Type*} [CommRing A] {n : ℕ}

theorem PI.OddDualWeyl.Intw.mul_transvection_apply (b a : Fin n) (c : A) (N : Matrix (Fin n) (Fin n) A) (p i : Fin n) :
    (N * transvection b a c) p i = N p i + if i = a then N p b * c else 0 := by sorry
