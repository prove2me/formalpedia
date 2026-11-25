-- Prove2me | Theorems.Thm_PI_ScRefExists_ApP_principal_ideal_ring_at_prime
-- name    : PI.ScRefExists.ApP.principal_ideal_ring_at_prime
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:22:29.741188+00:00
-- url     : https://prove2.me/theorems/51f03528-312e-40ed-941e-598fe86308e7
-- title:
--   Ap P: principal ideal ring at prime
-- statement:
--   The Ap P construction uses the principal ideal ring at prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/PrincipalIdealRingAtPrime.lean#L110-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/PrincipalIdealRingAtPrime.lean#L110-L115

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PrincipalIdealRingAtPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
open PI PI.ScRefExists PI.ScRefExists.ApP
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.ScRefExists.ApP.principal_ideal_ring_at_prime : ApPID := by sorry
