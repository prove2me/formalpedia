-- Prove2me | Theorems.Thm_PI_ScRefExists_ApP_pz_ne_bot
-- name    : PI.ScRefExists.ApP.pz_ne_bot
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:24:43.675034+00:00
-- url     : https://prove2.me/theorems/d0be70af-4f88-5c5d-a2a5-32113b465d9d
-- title:
--   Ap P: pz ne bot
-- statement:
--   The Ap P construction uses the pz ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/PrincipalIdealRingAtPrime.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/PrincipalIdealRingAtPrime.lean#L19-L21

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

theorem PI.ScRefExists.ApP.pz_ne_bot {p : ℕ} (hp : p.Prime) : Pz p ≠ ⊥ := by sorry
