-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_map_scx_LR
-- name    : PI.UnitaryGroupMassFormula.UsCost.map_scx_LR
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:37:00.653618+00:00
-- url     : https://prove2.me/theorems/0bacc78d-de73-53f3-b049-59fe33039afd
-- title:
--   Us Cost: map scx LR
-- statement:
--   The Us Cost construction uses the map scx LR property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/EntryLeLsz.lean#L99-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/EntryLeLsz.lean#L99-L101

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_EntryLeLsz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost

theorem PI.UnitaryGroupMassFormula.UsCost.map_scx_LR {k r : ℕ} (u v : List (B.Mat k r)) :
    (P.BetaSesquilinearity.wL u ++ P.BetaSesquilinearity.wR v).map scx = P.BetaSesquilinearity.wL (u.map sc) ++ P.BetaSesquilinearity.wR (v.map sc) := by sorry
