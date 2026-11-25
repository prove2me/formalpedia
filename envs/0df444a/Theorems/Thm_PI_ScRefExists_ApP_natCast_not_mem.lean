-- Prove2me | Theorems.Thm_PI_ScRefExists_ApP_natCast_not_mem
-- name    : PI.ScRefExists.ApP.natCast_not_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:22:27.153671+00:00
-- url     : https://prove2.me/theorems/7f4463cb-a8cd-458a-aa50-2d00ca4fe2a3
-- title:
--   Ap P: nat Cast not mem
-- statement:
--   The Ap P construction uses the nat Cast not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/PrincipalIdealRingAtPrime.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/PrincipalIdealRingAtPrime.lean#L23-L29

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

theorem PI.ScRefExists.ApP.natCast_not_mem {p : ℕ} (hp : p.Prime) {s : ℕ} (hs : Nat.Coprime s p) : (s : ℤ) ∉ Pz p := by sorry
