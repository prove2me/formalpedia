-- Prove2me | Theorems.Thm_PI_FJMD_dd_eq_zero
-- name    : PI.FJMD.dd_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:55.687133+00:00
-- url     : https://prove2.me/theorems/dbd82e4a-e2fa-4181-b38c-b16d15486af7
-- title:
--   FJMD: dd eq zero
-- statement:
--   The FJMD construction uses the dd eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeProdVarMatNeZero.lean#L101-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeProdVarMatNeZero.lean#L101-L110

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.FJMD
open PI.FJM

theorem PI.FJMD.dd_eq_zero {p q r s : ℕ} {S : Set (Ln p q r s)} {P : Pol p q r s}
    (hP : P ∈ MvPolynomial.supported ℂ S) {l l' : Ln p q r s} (h : l ∉ S ∨ l' ∉ S) : dd l l' P = 0 := by sorry
