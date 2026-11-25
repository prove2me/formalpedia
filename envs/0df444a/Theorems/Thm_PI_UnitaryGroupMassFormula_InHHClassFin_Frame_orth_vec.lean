-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_Frame_orth_vec
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.Frame.orth_vec
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:05:56.353981+00:00
-- url     : https://prove2.me/theorems/98b9702f-35b1-4e76-babe-f2cd2545c442
-- title:
--   Frame: orth vec
-- statement:
--   The Frame construction uses the orth vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L156-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L156-L164

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_HformSumRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix Formalism.UG PI.InHHClassFin
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)}

theorem PI.UnitaryGroupMassFormula.InHHClassFin.Frame.orth_vec (fr : Frame I S) (x : Fin fr.k → I.E) :
    ∀ s ∈ S, hform (starRingEnd I.E) I.J s (fr.B *ᵥ Sum.elim 0 x) = 0 := by sorry
