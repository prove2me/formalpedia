-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Intw_adjugate_transvection
-- name    : PI.OddDualWeyl.Intw.adjugate_transvection
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:14:19.314957+00:00
-- url     : https://prove2.me/theorems/d0386849-4ec9-4504-96bb-c11b57f3dd09
-- title:
--   Intw: adjugate transvection
-- statement:
--   The Intw construction uses the adjugate transvection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/TransvectionMulApply.lean#L31-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/TransvectionMulApply.lean#L31-L41

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

theorem PI.OddDualWeyl.Intw.adjugate_transvection {i j : Fin n} (h : i ≠ j) (c : A) :
    adjugate (transvection i j c) = transvection i j (-c) := by sorry
