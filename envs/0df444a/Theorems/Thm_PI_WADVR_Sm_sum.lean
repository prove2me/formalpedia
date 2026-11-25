-- Prove2me | Theorems.Thm_PI_WADVR_Sm_sum
-- name    : PI.WADVR.Sm.sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:44:14.352088+00:00
-- url     : https://prove2.me/theorems/a66c1ebc-e103-490b-80ad-60b4b8c3cb68
-- title:
--   Sm: sum
-- statement:
--   The Sm construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/RhoProjectionAssembly.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/RhoProjectionAssembly.lean#L10-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeakApproxDVR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_RhoProjectionAssembly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WADVR

theorem PI.WADVR.Sm.sum {W Q : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
    [Algebra W Q] [IsFractionRing W Q] {ϖ : W} {κ : Type*} (s : Finset κ) (f : κ → Q) (k : ℤ)
    (h : ∀ i ∈ s, Sm Q ϖ k (f i)) : Sm Q ϖ k (∑ i ∈ s, f i) := by sorry
