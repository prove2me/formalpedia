-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_top_prod_map_le
-- name    : PI.UnitaryGroupMassFormula.UsCost.top_prod_map_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:37:39.055452+00:00
-- url     : https://prove2.me/theorems/2ac67873-54ab-4d20-8ce7-5b4cb09d174c
-- title:
--   Us Cost: top prod map le
-- statement:
--   The Us Cost construction uses the top prod map le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/UnitarySumCostOfParts.lean#L10-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/UnitarySumCostOfParts.lean#L10-L23

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

theorem PI.UnitaryGroupMassFormula.UsCost.top_prod_map_le {α : Type*} (l : List α) (f : α → ℝ) (c : ℝ)
    (hf : ∀ x ∈ l, 0 ≤ f x ∧ f x ≤ c) (hc : 0 ≤ c) : (l.map f).prod ≤ c ^ l.length := by sorry
