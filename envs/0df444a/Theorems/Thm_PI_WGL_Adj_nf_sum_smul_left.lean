-- Prove2me | Theorems.Thm_PI_WGL_Adj_nf_sum_smul_left
-- name    : PI.WGL.Adj.nf_sum_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:59.828811+00:00
-- url     : https://prove2.me/theorems/6d0956b3-2e2d-4728-a5a3-d6a454c6eea3
-- title:
--   Adj: nf sum smul left
-- statement:
--   The Adj construction uses the nf sum smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/AdjBase.lean#L82-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/AdjBase.lean#L82-L86

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

theorem PI.WGL.Adj.nf_sum_smul_left {N : ℕ} (lam : DomWeight N) {ι : Type} (S : Finset ι) (a : ι → ℂ)
    (v : ι → MvPolynomial (Fin N × Fin N) ℂ) (g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (∑ k ∈ S, a k • v k) g = ∑ k ∈ S, a k * normFock lam (v k) g := by sorry
