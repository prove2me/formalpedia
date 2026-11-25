-- Prove2me | Theorems.Thm_PI_FockOneDegW_Core_shift_eq
-- name    : PI.FockOneDegW.Core.shift_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:30:45.590954+00:00
-- url     : https://prove2.me/theorems/81b11b32-f99a-4b8e-a6e7-dffb8655bed8
-- title:
--   Core: shift eq
-- statement:
--   The Core construction uses the shift eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L281-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L281-L321

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

theorem PI.FockOneDegW.Core.shift_eq (α : Ln p q r s →₀ ℕ)
    (hrow : ∀ (a : Ix p q) (c d : Ix r s), linePos ((a, c) : Ln p q r s) = false →
      linePos ((a, d) : Ln p q r s) = true → α (a, c) = 0 ∨ α (a, d) = 0) (a : Ix p q) :
    |shiftNu (cPair r s) (fun b => W1 b α) a| = ∑ c : Ix r s, (α (a, c) : ℚ) := by sorry
