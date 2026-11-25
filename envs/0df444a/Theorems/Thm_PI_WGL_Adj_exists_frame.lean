-- Prove2me | Theorems.Thm_PI_WGL_Adj_exists_frame
-- name    : PI.WGL.Adj.exists_frame
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:47:24.447934+00:00
-- url     : https://prove2.me/theorems/2cc047d1-87b5-4a35-9ef4-787143b52d60
-- title:
--   Adj: exists frame
-- statement:
--   The Adj construction uses the exists frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/AdjBase.lean#L173-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/AdjBase.lean#L173-L185

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitPowerNormScale_NormUnitsZpowSq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_AdjBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.Adj
open Formalism.BasicNotions MvPolynomial

theorem PI.WGL.Adj.exists_frame (n : ℕ) (sg : DomWeight n) :
    ∃ (d : ℕ) (b : Fin d → MvPolynomial (Fin n × Fin n) ℂ), (∀ k, b k ∈ nablaSq ℂ n sg) ∧
      ∀ s ∈ nablaSq ℂ n sg, s = ∑ k, normFock sg s (b k) • b k := by sorry
