-- Prove2me | Theorems.Thm_PI_ScRefExists_PPA_LA_clear
-- name    : PI.ScRefExists.PPA.LA_clear
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:58:35.316563+00:00
-- url     : https://prove2.me/theorems/ef973f88-74cc-4b52-82da-b9f936c48dfe
-- title:
--   PPA: LA clear
-- statement:
--   The PPA construction uses the LA clear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/NatCastSmulMemL.lean#L82-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/NatCastSmulMemL.lean#L82-L108

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_NatCastSmulMemL
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
open PI PI.ScRefExists PI.ScRefExists.PPA
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.ScRefExists.PPA.LA_clear (p : ℕ) {v : Fin I.n → I.E} (hv : v ∈ LA I p) :
    ∃ s : ℕ, Nat.Coprime s p ∧ (s : I.E) • v ∈ I.L := by sorry
