-- Prove2me | Theorems.Thm_PI_FockOneDegW_Core_core
-- name    : PI.FockOneDegW.Core.core
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:03:20.065794+00:00
-- url     : https://prove2.me/theorems/ac210886-a8c4-4851-b906-7b33958d3d53
-- title:
--   Core: core
-- statement:
--   The Core construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L226-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L226-L253

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
variable {p q r s : ℕ}

theorem PI.FockOneDegW.Core.core (hK : OpsK) (hL : HarmIff) (μ : Ix p q → ℚ) (v : Pol p q r s)
    (hv : IsHW (fockAct1 p q r s) μ v) (hh : Harm2 v) (a : Ix p q) (c d : Ix r s)
    (hc : linePos ((a, c) : Ln p q r s) = false) (hd : linePos ((a, d) : Ln p q r s) = true) :
    pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) v) = 0 := by sorry
