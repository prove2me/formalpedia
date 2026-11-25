-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Intw_coeff_comp_neg_X
-- name    : PI.OddDualWeyl.Intw.coeff_comp_neg_X
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:13:59.680864+00:00
-- url     : https://prove2.me/theorems/3a751222-12c4-5e5b-938b-b735be268091
-- title:
--   Intw: coeff comp neg X
-- statement:
--   The Intw construction uses the coeff comp neg X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/TransvectionMulApply.lean#L43-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/TransvectionMulApply.lean#L43-L57

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

theorem PI.OddDualWeyl.Intw.coeff_comp_neg_X (p : Polynomial A) (m : ℕ) :
    (p.comp (-Polynomial.X)).coeff m = (-1) ^ m * p.coeff m := by sorry
