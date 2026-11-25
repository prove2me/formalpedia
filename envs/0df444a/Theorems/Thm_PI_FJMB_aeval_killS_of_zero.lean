-- Prove2me | Theorems.Thm_PI_FJMB_aeval_killS_of_zero
-- name    : PI.FJMB.aeval_killS_of_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:30:26.513066+00:00
-- url     : https://prove2.me/theorems/c775baf5-57d1-4e00-851e-cf14c5bdf52f
-- title:
--   FJMB: aeval kill S of zero
-- statement:
--   The FJMB construction uses the aeval kill S of zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurElim.lean#L49-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurElim.lean#L49-L56

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}

theorem PI.FJMB.aeval_killS_of_zero {K : Type*} [CommRing K] [Algebra ℂ K] (S : Set σ) (y : σ → K)
    (hy : ∀ v ∈ S, y v = 0) (f : MvPolynomial σ ℂ) : aeval y (aeval (killS S) f) = aeval y f := by sorry
