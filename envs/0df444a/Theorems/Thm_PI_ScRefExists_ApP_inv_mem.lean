-- Prove2me | Theorems.Thm_PI_ScRefExists_ApP_inv_mem
-- name    : PI.ScRefExists.ApP.inv_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:24:38.122637+00:00
-- url     : https://prove2.me/theorems/fec67039-f07f-5364-9001-566d1fc105c9
-- title:
--   Ap P: inv mem
-- statement:
--   The Ap P construction uses the inv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/PrincipalIdealRingAtPrime.lean#L42-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/PrincipalIdealRingAtPrime.lean#L42-L58

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

theorem PI.ScRefExists.ApP.inv_mem {p : ℕ} (hp : p.Prime) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) : ((n : I.E))⁻¹ ∈ Ap I p := by sorry
