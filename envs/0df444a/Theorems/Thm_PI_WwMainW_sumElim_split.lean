-- Prove2me | Theorems.Thm_PI_WwMainW_sumElim_split
-- name    : PI.WwMainW.sumElim_split
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:46:18.617942+00:00
-- url     : https://prove2.me/theorems/9ff1617b-aed8-4438-a176-a03bf17ee686
-- title:
--   Ww Main W: sum Elim split
-- statement:
--   The Ww Main W construction uses the sum Elim split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionMinors/LfunEqOfSubset.lean#L74-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionMinors/LfunEqOfSubset.lean#L74-L78

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_FintypeColChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_LfunEqOfSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open PI PI.WwMainW
open PI.WwMain PI.WwMain.KM

theorem PI.WwMainW.sumElim_split {α β : Type} (μ : (α ⊕ β) →₀ ℕ) :
    μ = Finsupp.sumElim (Finsupp.sumFinsuppEquivProdFinsupp μ).1
      (Finsupp.sumFinsuppEquivProdFinsupp μ).2 := by sorry
