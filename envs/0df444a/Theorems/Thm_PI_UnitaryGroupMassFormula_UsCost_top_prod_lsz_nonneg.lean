-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_top_prod_lsz_nonneg
-- name    : PI.UnitaryGroupMassFormula.UsCost.top_prod_lsz_nonneg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:49:51.387571+00:00
-- url     : https://prove2.me/theorems/a1a2a4ae-782c-50c3-8573-2d2eab07c45c
-- title:
--   Us Cost: top prod lsz nonneg
-- statement:
--   The Us Cost construction uses the top prod lsz nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/UnitarySumCostOfParts.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/UnitarySumCostOfParts.lean#L29-L33

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_UnitarySumCostOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost

theorem PI.UnitaryGroupMassFormula.UsCost.top_prod_lsz_nonneg {k r : ℕ} (l : List (B.Mat k r)) : 0 ≤ (l.map lsz).prod := by sorry
