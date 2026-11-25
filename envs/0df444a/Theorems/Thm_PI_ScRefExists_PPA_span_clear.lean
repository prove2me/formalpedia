-- Prove2me | Theorems.Thm_PI_ScRefExists_PPA_span_clear
-- name    : PI.ScRefExists.PPA.span_clear
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:24:24.228271+00:00
-- url     : https://prove2.me/theorems/566f7306-8c3c-4751-98ac-9e8a62d8c83b
-- title:
--   PPA: span clear
-- statement:
--   The PPA construction uses the span clear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/NatCastSmulMemL.lean#L122-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/NatCastSmulMemL.lean#L122-L155

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

theorem PI.ScRefExists.PPA.span_clear (p : ℕ) (S : Set (Fin I.n → I.E)) {y : Fin I.n → I.E}
    (hy : y ∈ Submodule.span (Ap I p) S) :
    ∃ s : ℕ, Nat.Coprime s p ∧ (s : I.E) • y ∈ Submodule.span (𝓞 I.E) S := by sorry
