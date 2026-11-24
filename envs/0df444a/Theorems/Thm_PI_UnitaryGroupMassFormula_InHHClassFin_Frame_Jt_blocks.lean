-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_Frame_Jt_blocks
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.Frame.Jt_blocks
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:11:41.137771+00:00
-- url     : https://prove2.me/theorems/418a2d67-a1c6-433a-86aa-e5c85ef49eb0
-- title:
--   Frame: Jt blocks
-- statement:
--   The Frame construction uses the Jt blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L87-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L87-L90

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

theorem PI.UnitaryGroupMassFormula.InHHClassFin.Frame.Jt_blocks (fr : Frame I S) : fr.Jt = Matrix.fromBlocks fr.Jt.toBlocks₁₁ 0 0 fr.J' := by sorry
