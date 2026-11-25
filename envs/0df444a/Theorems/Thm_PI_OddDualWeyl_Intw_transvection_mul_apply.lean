-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Intw_transvection_mul_apply
-- name    : PI.OddDualWeyl.Intw.transvection_mul_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:14:14.118951+00:00
-- url     : https://prove2.me/theorems/0d23b8d1-cfc5-5048-af45-9572e0056083
-- title:
--   Intw: transvection mul apply
-- statement:
--   The Intw construction uses the transvection mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/TransvectionMulApply.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/TransvectionMulApply.lean#L16-L21

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

theorem PI.OddDualWeyl.Intw.transvection_mul_apply (b a : Fin n) (c : A) (N : Matrix (Fin n) (Fin n) A) (i s : Fin n) :
    (transvection b a c * N) i s = N i s + if i = b then c * N a s else 0 := by sorry
