-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_KerSplit_isIntegral_half
-- name    : PI.UnitaryGroupMassFormula.KerSplit.isIntegral_half
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:39:15.981088+00:00
-- url     : https://prove2.me/theorems/40bb5f7e-1c53-4583-bed2-e30fdad9aafd
-- title:
--   Ker Split: is Integral half
-- statement:
--   The Ker Split construction uses the is Integral half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KernelSplitting/IsIntegralHalf.lean#L16-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KernelSplitting/IsIntegralHalf.lean#L16-L28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualOfDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KernelSplitting_IsIntegralHalf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Polynomial
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.KerSplit

theorem PI.UnitaryGroupMassFormula.KerSplit.isIntegral_half {K : Type} [Field K] [CharZero K] (d : ℕ) (s : K) (hd : d % 8 = 7)
    (hs : s * s = -(d : K)) : IsIntegral ℤ ((1 + s) / 2) := by sorry
