-- Prove2me | Theorems.Thm_P2M_PI_SqfRootShift_W_aeval_eq_zero_of_dvd__aabcf90c1878
-- name    : P2M_PI_SqfRootShift_W_aeval_eq_zero_of_dvd__aabcf90c1878
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:58:15.706442+00:00
-- url     : https://prove2.me/theorems/b951f17f-50bf-4560-be40-6c7f81d54052
-- title:
--   P2 M PI Sqf Root Shift W aeval eq zero of dvd  aabcf90c1878: P2 M PI Sqf Root Shift W aeval eq zero of dvd  aabcf90c1878
-- statement:
--   The P2 M PI Sqf Root Shift W aeval eq zero of dvd  aabcf90c1878 construction uses the P2 M PI Sqf Root Shift W aeval eq zero of dvd  aabcf90c1878 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountB.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountB.lean#L34-L37

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]

theorem P2M_PI_SqfRootShift_W_aeval_eq_zero_of_dvd__aabcf90c1878 {P Q : (ZMod g)[X]} (h : P ∣ Q) {z : Fbar g}
    (hz : aeval z P = 0) : aeval z Q = 0 := by sorry

alias «PI».«SqfRootShift».«W».«aeval_eq_zero_of_dvd'» := P2M_PI_SqfRootShift_W_aeval_eq_zero_of_dvd__aabcf90c1878
