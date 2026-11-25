-- Prove2me | Theorems.Thm_PI_FockOneDegW_Core_coeff_zero_of_dd
-- name    : PI.FockOneDegW.Core.coeff_zero_of_dd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:31:13.145227+00:00
-- url     : https://prove2.me/theorems/dcab0702-c9da-5e63-a9ca-f3dfff92ce14
-- title:
--   Core: coeff zero of dd
-- statement:
--   The Core construction uses the coeff zero of dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L36-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L36-L56

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.Core
open PI.FockOneDegW PI.FockOneDegW.Inner PI.FockOneDegW.Diag

theorem PI.FockOneDegW.Core.coeff_zero_of_dd {σ : Type*} (v : MvPolynomial σ ℂ) (i j : σ) (hij : i ≠ j)
    (h : pderiv i (pderiv j v) = 0) (α : σ →₀ ℕ) (hα : coeff α v ≠ 0) :
    α i = 0 ∨ α j = 0 := by sorry
