-- Prove2me | Theorems.Thm_PI_BeDiagZp_SubstW_constantCoeff_lift
-- name    : PI.BeDiagZp.SubstW.constantCoeff_lift
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:24:34.518716+00:00
-- url     : https://prove2.me/theorems/e32cdb34-fef9-51b5-8c2a-b69c96719852
-- title:
--   Subst W: constant Coeff lift
-- statement:
--   The Subst W construction uses the constant Coeff lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L45-L52

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_PowerSeriesDiagonalLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BeDiagZp PI.BeDiagZp.SubstW

theorem PI.BeDiagZp.SubstW.constantCoeff_lift {K : Type*} [CommRing K] (S : Subring K) {σ : Type*}
    (g : MvPowerSeries σ S) {c : S}
    (h : MvPowerSeries.constantCoeff (MvPowerSeries.map S.subtype g) = (c : K)) :
    MvPowerSeries.constantCoeff g = c := by sorry
