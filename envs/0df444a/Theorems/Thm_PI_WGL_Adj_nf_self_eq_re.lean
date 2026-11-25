-- Prove2me | Theorems.Thm_PI_WGL_Adj_nf_self_eq_re
-- name    : PI.WGL.Adj.nf_self_eq_re
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:47:10.792829+00:00
-- url     : https://prove2.me/theorems/f135a6c9-171b-40f6-b8ff-d38568596c48
-- title:
--   Adj: nf self eq re
-- statement:
--   The Adj construction uses the nf self eq re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/AdjBase.lean#L128-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/AdjBase.lean#L128-L130

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

theorem PI.WGL.Adj.nf_self_eq_re {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f f = (((normFock lam f f).re : ℝ) : ℂ) := by sorry
