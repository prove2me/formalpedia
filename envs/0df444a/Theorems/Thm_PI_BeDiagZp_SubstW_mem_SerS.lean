-- Prove2me | Theorems.Thm_PI_BeDiagZp_SubstW_mem_SerS
-- name    : PI.BeDiagZp.SubstW.mem_SerS
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:24:54.991298+00:00
-- url     : https://prove2.me/theorems/0c8b5309-961c-43d6-9205-c65cdfd1a068
-- title:
--   Subst W: mem Ser S
-- statement:
--   The Subst W construction uses the mem Ser S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L31-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L31-L43

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

theorem PI.BeDiagZp.SubstW.mem_SerS {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} (f : MvPowerSeries σ K) :
    f ∈ SerS S σ ↔ ∀ e, MvPowerSeries.coeff e f ∈ S := by sorry
