-- Prove2me | Theorems.Thm_PI_ScRefExists_PPA_hG_mem_Ap
-- name    : PI.ScRefExists.PPA.hG_mem_Ap
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:22:38.741401+00:00
-- url     : https://prove2.me/theorems/de8efa42-69b2-551f-8ae4-3f216f54f051
-- title:
--   PPA: h G mem Ap
-- statement:
--   The PPA construction uses the h G mem Ap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/NatCastSmulMemL.lean#L110-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/NatCastSmulMemL.lean#L110-L120

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

theorem PI.ScRefExists.PPA.hG_mem_Ap (p : ℕ) {v v' : Fin I.n → I.E} (hv : v ∈ LA I p) (hv' : v' ∈ LA I p) :
    hG I v v' ∈ Ap I p := by sorry
