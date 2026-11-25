-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_bS_last
-- name    : PI.UnitaryGroupMassFormula.QmBorderFull.bS_last
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:40:16.692799+00:00
-- url     : https://prove2.me/theorems/069b2d89-a256-48c5-ac6d-16264dc16a4b
-- title:
--   Qm Border Full: b S last
-- statement:
--   The Qm Border Full construction uses the b S last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipOneEqSuccAbove.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipOneEqSuccAbove.lean#L38-L39

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

theorem PI.UnitaryGroupMassFormula.QmBorderFull.bS_last {n m : ℕ} (v : Fin m → Fin n) (es : Fin n) : bS v es (Fin.last m) = es := by sorry
