-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_bS_castSucc
-- name    : PI.UnitaryGroupMassFormula.QmBorderFull.bS_castSucc
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:41:13.358594+00:00
-- url     : https://prove2.me/theorems/cb722d75-06ed-4294-a414-bd60e3fccec2
-- title:
--   Qm Border Full: b S cast Succ
-- statement:
--   The Qm Border Full construction uses the b S cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipOneEqSuccAbove.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipOneEqSuccAbove.lean#L34-L36

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipOneEqSuccAbove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull
open PI

theorem PI.UnitaryGroupMassFormula.QmBorderFull.bS_castSucc {n m : ℕ} (v : Fin m → Fin n) (es : Fin n) : bS v es ∘ Fin.castSucc = v := by sorry
