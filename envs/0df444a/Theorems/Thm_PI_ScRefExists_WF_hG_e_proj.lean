-- Prove2me | Theorems.Thm_PI_ScRefExists_WF_hG_e_proj
-- name    : PI.ScRefExists.WF.hG_e_proj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:15:50.056934+00:00
-- url     : https://prove2.me/theorems/f0fa09b6-c7f2-4b05-af02-2f6804a4df6b
-- title:
--   WF: h G e proj
-- statement:
--   The WF construction uses the h G e proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/MemLAOfNsmul.lean#L112-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/MemLAOfNsmul.lean#L112-L132

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_MemLAOfNsmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open PI PI.ScRefExists PI.ScRefExists.WF
variable {I : Formalism.MainNotions.S.AutInst} {p : ℕ}

theorem PI.ScRefExists.WF.hG_e_proj {r : ℕ} {e f : Fin r → Fin I.n → I.E} (he : ∀ a b, hG I (e a) (e b) = 0)
    (hef : ∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) (b : Fin r) (y : Fin I.n → I.E) :
    hG I (e b) (proj e f y) = hG I (e b) y := by sorry
