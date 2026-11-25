-- Prove2me | Theorems.Thm_PI_GGCardUniWork_cardUni
-- name    : PI.GGCardUniWork.cardUni
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:48.446784+00:00
-- url     : https://prove2.me/theorems/8f4933ef-8c54-4068-9b1f-052443f2efc9
-- title:
--   GGCard Uni Work: card Uni
-- statement:
--   The GGCard Uni Work construction uses the card Uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCardinality/UniMatUpper.lean#L66-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCardinality/UniMatUpper.lean#L66-L70

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCardinality_UniMatUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGCardUniWork
open Finset Matrix Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}

theorem PI.GGCardUniWork.cardUni : CardUni := by sorry
