-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_KerSplit_splitsAt_two
-- name    : PI.UnitaryGroupMassFormula.KerSplit.splitsAt_two
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:39:02.695872+00:00
-- url     : https://prove2.me/theorems/317fdc23-fe3f-5a95-b46d-fcdde34c3870
-- title:
--   Ker Split: splits At two
-- statement:
--   The Ker Split construction uses the splits At two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KernelSplitting/IsIntegralHalf.lean#L60-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KernelSplitting/IsIntegralHalf.lean#L60-L94

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

theorem PI.UnitaryGroupMassFormula.KerSplit.splitsAt_two {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (cj : E ≃ₐ[ℚ] E) (d : ℕ) (s : K) (hd : d % 8 = 7) (hs : s * s = -(d : K))
    (hcj : cj (algebraMap K E s) = -algebraMap K E s) : PI.KerIso.SplitsAt K cj 2 := by sorry
