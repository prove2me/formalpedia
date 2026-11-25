-- Prove2me | Theorems.Thm_PI_ScRefExists_PPA_GE_of_QA
-- name    : PI.ScRefExists.PPA.GE_of_QA
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:36.976077+00:00
-- url     : https://prove2.me/theorems/d28f438c-3236-42d7-a387-2ceb40de6729
-- title:
--   PPA: GE of QA
-- statement:
--   The PPA construction uses the GE of QA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/NatCastSmulMemL.lean#L189-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/NatCastSmulMemL.lean#L189-L206

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

theorem PI.ScRefExists.PPA.GE_of_QA (p m : ℕ) {x : I.E} (hint : ∃ a : 𝓞 I.E, (a : I.E) = x) (h : QA I p (p ^ m) x) :
    GE I (p ^ m) x := by sorry
