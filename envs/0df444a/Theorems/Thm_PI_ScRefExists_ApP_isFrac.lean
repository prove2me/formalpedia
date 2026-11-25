-- Prove2me | Theorems.Thm_PI_ScRefExists_ApP_isFrac
-- name    : PI.ScRefExists.ApP.isFrac
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:02.25542+00:00
-- url     : https://prove2.me/theorems/5ce0ca5d-7f22-447f-8379-073bb143e810
-- title:
--   Ap P: is Frac
-- statement:
--   The Ap P construction uses the is Frac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/PrincipalIdealRingAtPrime.lean#L117-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/PrincipalIdealRingAtPrime.lean#L117-L120

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

theorem PI.ScRefExists.ApP.isFrac {p : ℕ} [Fact p.Prime] : IsFractionRing (Ap I p) I.E := by sorry
