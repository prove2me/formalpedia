-- Prove2me | Theorems.Thm_PI_WGL_Adj_nf_sum_smul_right
-- name    : PI.WGL.Adj.nf_sum_smul_right
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:58:20.020805+00:00
-- url     : https://prove2.me/theorems/bb67243a-b0cf-5f0f-bc84-167e086af04d
-- title:
--   Adj: nf sum smul right
-- statement:
--   The Adj construction uses the nf sum smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/AdjBase.lean#L88-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/AdjBase.lean#L88-L93

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

theorem PI.WGL.Adj.nf_sum_smul_right {N : ℕ} (lam : DomWeight N) {ι : Type} (S : Finset ι) (a : ι → ℂ)
    (v : ι → MvPolynomial (Fin N × Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f (∑ k ∈ S, a k • v k) = ∑ k ∈ S, star (a k) * normFock lam f (v k) := by sorry
