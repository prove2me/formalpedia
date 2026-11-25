-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_KerSplit_splitsAt_odd
-- name    : PI.UnitaryGroupMassFormula.KerSplit.splitsAt_odd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:39:06.547853+00:00
-- url     : https://prove2.me/theorems/050f5241-55be-42f1-a15b-6c234a794007
-- title:
--   Ker Split: splits At odd
-- statement:
--   The Ker Split construction uses the splits At odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KernelSplitting/IsIntegralHalf.lean#L96-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KernelSplitting/IsIntegralHalf.lean#L96-L169

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

theorem PI.UnitaryGroupMassFormula.KerSplit.splitsAt_odd {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (cj : E ≃ₐ[ℚ] E) (d p : ℕ) (s : K) (hs : s * s = -(d : K))
    (hcj : cj (algebraMap K E s) = -algebraMap K E s) (hp : p.Prime) (hp2 : p ≠ 2)
    (hJ : jacobiSym (-(d : ℤ)) p = 1) : PI.KerIso.SplitsAt K cj p := by sorry
